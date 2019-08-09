-- Copyright 2019 Stanford University
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

-- Regent Index Launch Optimizer
--
-- Attempts to determine which loops can be transformed into index
-- space task launches.

local affine_helper = require("regent/affine_helper")
local ast = require("regent/ast")
local data = require("common/data")
local report = require("common/report")
local std = require("regent/std")

local context = {}

function context:__index (field)
  local value = context [field]
  if value ~= nil then
    return value
  end
  error ("context has no field '" .. field .. "' (in lookup)", 2)
end

function context:__newindex (field, value)
  error ("context has no field '" .. field .. "' (in assignment)", 2)
end

function context:new_local_scope()
  local cx = {
    constraints = self.constraints,
    loop_index = false,
    loop_variables = {},
    free_variables = terralib.newlist(),
  }
  return setmetatable(cx, context)
end

function context:new_task_scope(constraints)
  local cx = {
    constraints = constraints,
  }
  return setmetatable(cx, context)
end

function context.new_global_scope()
  local cx = {}
  return setmetatable(cx, context)
end

function context:set_loop_index(loop_index)
  assert(not self.loop_index)
  self.loop_index = loop_index
end

function context:add_loop_variable(loop_variable)
  assert(self.loop_variables)
  self.loop_variables[loop_variable] = true
end

function context:add_free_variable(symbol)
  assert(self.free_variables)
  self.free_variables:insert(symbol)
end

function context:is_free_variable(variable)
  assert(self.free_variables)
  for _,elem in ipairs(self.free_variables) do
    if tostring(elem) == tostring(variable) then
      return true
    end
  end
  return false
end

function context:is_loop_variable(variable)
  assert(self.loop_variables)
  return self.loop_variables[variable]
end

function context:is_loop_index(variable)
  assert(self.loop_index)
  return self.loop_index == variable
end

local function check_privilege_noninterference(cx, task, arg,
                                         other_arg, mapping)
  local region_type = std.as_read(arg.expr_type)
  local other_region_type = std.as_read(other_arg.expr_type)
  local param_region_type = mapping[arg]
  local other_param_region_type = mapping[other_arg]
  assert(param_region_type and other_param_region_type)

  local privileges_by_field_path, coherence_modes_by_field_path =
    std.group_task_privileges_by_field_path(
      std.find_task_privileges(param_region_type, task))
  local other_privileges_by_field_path, other_coherence_modes_by_field_path =
    std.group_task_privileges_by_field_path(
      std.find_task_privileges(other_param_region_type, task))

  for field_path, privilege in pairs(privileges_by_field_path) do
    local other_privilege = other_privileges_by_field_path[field_path]

    if not (
        not privilege or privilege == "none" or
        not other_privilege or other_privilege == "none" or
        (privilege == "reads" and other_privilege == "reads") or
        (std.is_reduction_op(privilege) and privilege == other_privilege) or
        (coherence_modes_by_field_path[field_path] == "simultaneous" and
         other_coherence_modes_by_field_path[field_path] == "simultaneous"))
    then
      return false
    end
  end
  return true
end

local function strip_casts(node)
  if node:is(ast.typed.expr.Cast) then
    return node.arg
  end
  return node
end

local function analyze_noninterference_previous(
    cx, task, arg, regions_previously_used, mapping)
  local region_type = std.as_read(arg.expr_type)
  for i, other_arg in pairs(regions_previously_used) do
    local other_region_type = std.as_read(other_arg.expr_type)
    local constraint = std.constraint(
      region_type,
      other_region_type,
      std.disjointness)
    local exclude_variables = { [cx.loop_index] = true }

    if not (
        not std.type_maybe_eq(region_type.fspace_type, other_region_type.fspace_type) or
        std.check_constraint(cx, constraint, exclude_variables) or
        check_privilege_noninterference(cx, task, arg, other_arg, mapping))
        -- Index non-interference is handled at the type checker level
        -- and is captured in the constraints.
    then
      return false, i
    end
  end
  return true
end

--returns coefficient of loop_index. Non-interfering if non-zero
function analyze_expr_noninterference_self(expression, cx, loop_vars, report_fail, field_name)
  local expr = strip_casts(expression)

  if expr:is(ast.typed.expr.ID) then
    if cx:is_loop_variable(expr.value) then
      for _,loop_var in ipairs(loop_vars) do
          if loop_var.symbol == expr.value then
            return analyze_expr_noninterference_self(loop_var.value, cx, loop_vars, report_fail, field_name)
        end
      end
      -- DELETE ME
      print("analyzing noninterference... something done fucked up with loop var")
    elseif expr == cx.loop_index then
      return {
        value = 1,
        noninterfering = true,
        valid = true,
      }
    else
      -- invariant; inconclusive
      return {
        value = false,
        noninterfering = false,
        valid = true,
      }
    end

  elseif expr:is(ast.typed.expr.Binary) then
    local left_const = affine_helper.is_constant_expr(expr.lhs) and affine_helper.convert_constant_expr(expr.lhs)
    local right_const = affine_helper.is_constant_expr(expr.rhs) and affine_helper.convert_constant_expr(expr.rhs)
    local left = left_const and {
      value = left_const,
      noninterfering = false,
      valid = true,
      } or analyze_expr_noninterference_self(expr.lhs, cx, loop_vars, report_fail, field_name)
    local right =  right_const and {
      value = right_const,
      noninterfering = false,
      valid = true,
    } or analyze_expr_noninterference_self(expr.rhs, cx, loop_vars, report_fail, field_name)


    if expr.op == "+" then
      local valid = left.valid and right.valid and ((left.noninterfering ~= right.noninterfering) or (left.value and right.value))
      return {
        value = valid and (left.value and right.value)
                and ((left.valid or right.valid) and ((left.valid and left.value or 0) + (right.valid and right.value or 0))
                or (left.value + right.value)),
        noninterfering = valid and (left.noninterfering and right.noninterfering),
        valid = valid,
      }
    
    elseif expr.op == "-" then
      local valid = left.valid and right.valid and ((left.noninterfering ~= right.noninterfering) or (left.value and right.value))
      return {
        value = valid and (left.value and right.value)
                and ((left.valid or right.valid) and ((left.valid and left.value or 0) - (right.valid and right.value or 0))
                or (left.value - right.value)),
        noninterfering = valid and (left.noninterfering and right.noninterfering),
        valid = valid,
      }

    elseif expr.op == "*" then
      local valid = left.valid and right.valid and (not (left.noninterfering and right.noninterfering)) and ( (left.value or left.noninterfering) and (right.value or right.noninterfering) or (not (left.noninterfering or right.noninterfering)))
      return {
        value = valid and (left.value and right.value) and (left.value * right.value),
        noninterfering = valid and (left.noninterfering or right.noninterfering),
        valid = valid,
      }
      
    -- TODO: add mod operator check
    else
      return {
        value = false,
        noninterfering = false,
        valid = false,
      }
    end

  elseif expr:is(ast.typed.expr.Ctor) then
    -- DELETE ME
    print("optimize_index_launch noninterself: Ctor")
    local loop_index_type = cx.loop_index:gettype()
    if loop_index_type.fields then

      for _, loop_index_field in ipairs(loop_index_type.fields) do
        -- DELETE ME
        print("optimize_index_launch Ctor: searching for field "..loop_index_field)
        local field_present = false
        for _, ctor_field in ipairs(expr.fields) do
          local arg_result = analyze_expr_noninterference_self(ctor_field.value, cx, loop_vars, report_fail, loop_index_field)
          if arg_result.noninterfering and (not arg_result.value or arg_result.value ~= 0) then
            field_present = true
            break
          end
        end
        if not field_present then
          -- DELETE ME
          print("optimize_index_launch Ctor: field "..loop_index_field.." not found")
          return {
            value = false,
            noninterfering = false,
            valid = false,
          }
        end
      end

      -- DELETE ME
      print("optimize_index_launch Ctor: all fields found")
      return {
        value = false,
        noninterfering = true,
        valid = true,
      }
    end

  elseif expr:is(ast.typed.expr.FieldAccess) then
    local id = expr.value
    local valid = cx.loop_index == id.value
                  and field_name == expr.field_name
    return {
      value = valid and 1,
      noninterfering = valid,
      valid = valid,
    }
  end

  return {
    value = false,
    noninterfering = false,
    valid = false,
  }
end

local function analyze_index_noninterference_self(expr, cx, loop_vars, report_fail, field_name)
  local result = analyze_expr_noninterference_self(expr, cx, loop_vars, report_fail, field_name)
  return result.valid and result.value ~= 0
end

local function analyze_noninterference_self(
    cx, task, arg, partition_type, mapping, loop_vars)
  local region_type = std.as_read(arg.expr_type)
  if partition_type and partition_type:is_disjoint() and
    analyze_index_noninterference_self(arg.index, cx, loop_vars)
  then
    return true
  end

  local param_region_type = mapping[arg]
  assert(param_region_type)
  local privileges, privilege_field_paths, privilege_field_types,
        privilege_coherence_modes, privilege_flags = std.find_task_privileges(
    param_region_type, task)
  for i, privilege in ipairs(privileges) do
    local field_paths = privilege_field_paths[i]
    local coherence = privilege_coherence_modes[i]
    if not (
        privilege == "none" or
        privilege == "reads" or
        std.is_reduction_op(privilege) or
        coherence == "simultaneous" or
        #field_paths == 0)
    then
      return false
    end
  end
  return true
end

local function analyze_is_side_effect_free_node(cx)
  return function(node)
    -- Expressions:
    if node:is(ast.typed.expr.IndexAccess) then
      return not std.is_ref(node.expr_type)
    elseif node:is(ast.typed.expr.Call) then
      return not std.is_task(node.fn.value)
    elseif node:is(ast.typed.expr.RawContext) or
      node:is(ast.typed.expr.RawPhysical) or
      node:is(ast.typed.expr.RawRuntime) or
      node:is(ast.typed.expr.Ispace) or
      node:is(ast.typed.expr.Region) or
      node:is(ast.typed.expr.Partition) or
      node:is(ast.typed.expr.PartitionEqual) or
      node:is(ast.typed.expr.PartitionByField) or
      node:is(ast.typed.expr.Image) or
      node:is(ast.typed.expr.Preimage) or
      node:is(ast.typed.expr.CrossProduct) or
      node:is(ast.typed.expr.ListSlicePartition) or
      node:is(ast.typed.expr.ListDuplicatePartition) or
      node:is(ast.typed.expr.ListSliceCrossProduct) or
      node:is(ast.typed.expr.ListCrossProduct) or
      node:is(ast.typed.expr.ListCrossProductComplete) or
      node:is(ast.typed.expr.ListPhaseBarriers) or
      node:is(ast.typed.expr.PhaseBarrier) or
      node:is(ast.typed.expr.DynamicCollective) or
      node:is(ast.typed.expr.Adjust) or
      node:is(ast.typed.expr.Arrive) or
      node:is(ast.typed.expr.Await) or
      node:is(ast.typed.expr.Copy) or
      node:is(ast.typed.expr.Fill) or
      node:is(ast.typed.expr.Acquire) or
      node:is(ast.typed.expr.Release) or
      node:is(ast.typed.expr.AllocateScratchFields) or
      node:is(ast.typed.expr.Condition) or
      node:is(ast.typed.expr.Deref)
    then
      return false

    elseif node:is(ast.typed.expr.ID) or
      node:is(ast.typed.expr.Constant) or
      node:is(ast.typed.expr.Function) or
      node:is(ast.typed.expr.FieldAccess) or
      node:is(ast.typed.expr.MethodCall) or
      node:is(ast.typed.expr.Cast) or
      node:is(ast.typed.expr.Ctor) or
      node:is(ast.typed.expr.CtorListField) or
      node:is(ast.typed.expr.CtorRecField) or
      node:is(ast.typed.expr.RawFields) or
      node:is(ast.typed.expr.RawValue) or
      node:is(ast.typed.expr.Isnull) or
      node:is(ast.typed.expr.Null) or
      node:is(ast.typed.expr.DynamicCast) or
      node:is(ast.typed.expr.StaticCast) or
      node:is(ast.typed.expr.UnsafeCast) or
      node:is(ast.typed.expr.ListInvert) or
      node:is(ast.typed.expr.ListRange) or
      node:is(ast.typed.expr.DynamicCollectiveGetResult) or
      node:is(ast.typed.expr.Advance) or
      node:is(ast.typed.expr.WithScratchFields) or
      node:is(ast.typed.expr.RegionRoot) or
      node:is(ast.typed.expr.Unary) or
      node:is(ast.typed.expr.Binary)
    then
      return true

    -- Statements:
    elseif node:is(ast.typed.stat.Var) then
      return true

    -- Miscellaneous:
    elseif node:is(ast.location) or
      node:is(ast.annotation) or
      node:is(ast.condition_kind)
    then
      return true

    else
      assert(false, "unexpected node type " .. tostring(node.node_type))
    end
  end
end

local function analyze_is_side_effect_free(cx, node)
  return ast.mapreduce_node_postorder(
    analyze_is_side_effect_free_node(cx),
    data.all,
    node, true)
end

local function analyze_is_loop_invariant_node(cx)
  return function(node)
    -- Expressions:
    if node:is(ast.typed.expr.ID) then
      if not std.is_region(node.value:gettype()) and
         not std.is_partition(node.value:gettype()) and
         not cx:is_loop_variable(node.value) and
         not cx:is_free_variable(node.value) then
        cx:add_free_variable(node.value)
        -- DELETE ME
        print("optimize_index_launch loop invariant ID?")
        print(node)
      end
      return not cx:is_loop_variable(node.value)
    elseif node:is(ast.typed.expr.IndexAccess) then
      return not std.is_ref(node.expr_type)
    elseif node:is(ast.typed.expr.Call) or
      node:is(ast.typed.expr.Ispace) or
      node:is(ast.typed.expr.Region) or
      node:is(ast.typed.expr.Partition) or
      node:is(ast.typed.expr.PartitionEqual) or
      node:is(ast.typed.expr.PartitionByField) or
      node:is(ast.typed.expr.Image) or
      node:is(ast.typed.expr.Preimage) or
      node:is(ast.typed.expr.CrossProduct) or
      node:is(ast.typed.expr.ListSlicePartition) or
      node:is(ast.typed.expr.ListDuplicatePartition) or
      node:is(ast.typed.expr.ListSliceCrossProduct) or
      node:is(ast.typed.expr.ListCrossProduct) or
      node:is(ast.typed.expr.ListCrossProductComplete) or
      node:is(ast.typed.expr.ListPhaseBarriers) or
      node:is(ast.typed.expr.PhaseBarrier) or
      node:is(ast.typed.expr.DynamicCollective) or
      node:is(ast.typed.expr.DynamicCollectiveGetResult) or
      node:is(ast.typed.expr.Adjust) or
      node:is(ast.typed.expr.Arrive) or
      node:is(ast.typed.expr.Await) or
      node:is(ast.typed.expr.Copy) or
      node:is(ast.typed.expr.Fill) or
      node:is(ast.typed.expr.Acquire) or
      node:is(ast.typed.expr.Release) or
      node:is(ast.typed.expr.AllocateScratchFields) or
      node:is(ast.typed.expr.Condition) or
      node:is(ast.typed.expr.Deref)
    then
      return false

    elseif node:is(ast.typed.expr.Constant) or
      node:is(ast.typed.expr.Function) or
      node:is(ast.typed.expr.FieldAccess) or
      node:is(ast.typed.expr.MethodCall) or
      node:is(ast.typed.expr.Cast) or
      node:is(ast.typed.expr.Ctor) or
      node:is(ast.typed.expr.CtorListField) or
      node:is(ast.typed.expr.CtorRecField) or
      node:is(ast.typed.expr.RawContext) or
      node:is(ast.typed.expr.RawFields) or
      node:is(ast.typed.expr.RawPhysical) or
      node:is(ast.typed.expr.RawRuntime) or
      node:is(ast.typed.expr.RawValue) or
      node:is(ast.typed.expr.Isnull) or
      node:is(ast.typed.expr.Null) or
      node:is(ast.typed.expr.DynamicCast) or
      node:is(ast.typed.expr.StaticCast) or
      node:is(ast.typed.expr.UnsafeCast) or
      node:is(ast.typed.expr.ListInvert) or
      node:is(ast.typed.expr.ListRange) or
      node:is(ast.typed.expr.Advance) or
      node:is(ast.typed.expr.WithScratchFields) or
      node:is(ast.typed.expr.RegionRoot) or
      node:is(ast.typed.expr.Unary) or
      node:is(ast.typed.expr.Binary)
    then
      return true

    -- Miscellaneous:
    elseif node:is(ast.location) or
      node:is(ast.annotation) or
      node:is(ast.condition_kind)
    then
      return true

    else
      assert(false, "unexpected node type " .. tostring(node.node_type))
    end
  end
end

local function analyze_is_loop_invariant(cx, node)
  return ast.mapreduce_node_postorder(
    analyze_is_loop_invariant_node(cx),
    data.all,
    node, true)
end

local function analyze_is_simple_index_expression_node(cx)
  return function(node)
    -- Expressions:
    if node:is(ast.typed.expr.ID) then
      return true

    elseif node:is(ast.typed.expr.FieldAccess) then
      -- Field access gets desugared in the type checker, just sanity
      -- check here that we're not doing a region access.
      local value_type = std.as_read(node.value.expr_type)
      assert(not std.is_bounded_type(value_type) or std.get_field(value_type.index_type.base_type, node.field_name))

    elseif node:is(ast.typed.expr.IndexAccess) or
      node:is(ast.typed.expr.MethodCall) or
      node:is(ast.typed.expr.Call) or
      node:is(ast.typed.expr.RawContext) or
      node:is(ast.typed.expr.RawFields) or
      node:is(ast.typed.expr.RawPhysical) or
      node:is(ast.typed.expr.RawRuntime) or
      node:is(ast.typed.expr.RawValue) or
      node:is(ast.typed.expr.Isnull) or
      node:is(ast.typed.expr.Null) or
      node:is(ast.typed.expr.DynamicCast) or
      node:is(ast.typed.expr.StaticCast) or
      node:is(ast.typed.expr.UnsafeCast) or
      node:is(ast.typed.expr.Ispace) or
      node:is(ast.typed.expr.Region) or
      node:is(ast.typed.expr.Partition) or
      node:is(ast.typed.expr.PartitionEqual) or
      node:is(ast.typed.expr.PartitionByField) or
      node:is(ast.typed.expr.Image) or
      node:is(ast.typed.expr.Preimage) or
      node:is(ast.typed.expr.CrossProduct) or
      node:is(ast.typed.expr.ListSlicePartition) or
      node:is(ast.typed.expr.ListDuplicatePartition) or
      node:is(ast.typed.expr.ListSliceCrossProduct) or
      node:is(ast.typed.expr.ListCrossProduct) or
      node:is(ast.typed.expr.ListCrossProductComplete) or
      node:is(ast.typed.expr.ListPhaseBarriers) or
      node:is(ast.typed.expr.ListInvert) or
      node:is(ast.typed.expr.ListRange) or
      node:is(ast.typed.expr.PhaseBarrier) or
      node:is(ast.typed.expr.DynamicCollective) or
      node:is(ast.typed.expr.DynamicCollectiveGetResult) or
      node:is(ast.typed.expr.Advance) or
      node:is(ast.typed.expr.Adjust) or
      node:is(ast.typed.expr.Arrive) or
      node:is(ast.typed.expr.Await) or
      node:is(ast.typed.expr.Copy) or
      node:is(ast.typed.expr.Fill) or
      node:is(ast.typed.expr.Acquire) or
      node:is(ast.typed.expr.Release) or
      node:is(ast.typed.expr.AllocateScratchFields) or
      node:is(ast.typed.expr.WithScratchFields) or
      node:is(ast.typed.expr.RegionRoot) or
      node:is(ast.typed.expr.Condition) or
      node:is(ast.typed.expr.Deref)
    then
      return false

    elseif node:is(ast.typed.expr.Constant) or
      node:is(ast.typed.expr.Function) or
      node:is(ast.typed.expr.Cast) or
      node:is(ast.typed.expr.Ctor) or
      node:is(ast.typed.expr.CtorListField) or
      node:is(ast.typed.expr.CtorRecField) or
      node:is(ast.typed.expr.Unary) or
      node:is(ast.typed.expr.Binary)
    then
      return true

    -- Miscellaneous:
    elseif node:is(ast.location) or
      node:is(ast.annotation) or
      node:is(ast.condition_kind)
    then
      return true

    else
      assert(false, "unexpected node type " .. tostring(node.node_type))
    end
  end
end

local function analyze_is_simple_index_expression(cx, node)
  return ast.mapreduce_node_postorder(
    analyze_is_simple_index_expression_node(cx),
    data.all,
    node, true)
end

local function analyze_is_projectable(cx, arg)
print("Projectable: is IndexAccess? "..(arg:is(ast.typed.expr.IndexAccess) and "yes" or "no"))
  -- 1. We can project any index access `p[...]`
  if not arg:is(ast.typed.expr.IndexAccess) then
    return false
  end

print("Projectable: is partition of cross product? "..((std.is_partition(std.as_read(arg.value.expr_type)) or std.is_cross_product(std.as_read(arg.value.expr_type))) and "yes" or "no"))
  -- 2. As long as `p` is a partition or cross product (otherwise this
  -- is irrelevant, since we wouldn't be producing a region requirement).
  if not (std.is_partition(std.as_read(arg.value.expr_type)) or
       std.is_cross_product(std.as_read(arg.value.expr_type)))
  then
    return false
  end

print("Projectable: is loop invariant? "..(analyze_is_loop_invariant(cx, arg.value) and "yes" or "no"))
  -- 3. And as long as `p` is loop-invariant (we have to index from
  -- the same partition every time).
  if not analyze_is_loop_invariant(cx, arg.value) then
    return false
  end

  -- 4. And as long as the index itself is a simple expression of the
  -- loop index.

print("Projectable: is simple index expr (is PROJECTABLE)? "..(analyze_is_simple_index_expression(cx, arg.index) and "yes" or "no"))

  return analyze_is_simple_index_expression(cx, arg.index)
end

local optimize_index_launch = {}
local optimize_index_launches = {}

local function ignore(...) end

local function optimize_loop_body(cx, node, report_pass, report_fail)
  if #node.block.stats == 0 then
    report_fail(node, "loop optimization failed: body is empty")
    return
  end

  local loop_cx = cx:new_local_scope()
  loop_cx:set_loop_index(node.symbol)
  loop_cx:add_loop_variable(node.symbol)

  local preamble = terralib.newlist()
  -- vars that need to be defined within projection functor
  local loop_vars = terralib.newlist()
  local call_stat
  for i = 1, #node.block.stats - 1 do
    local stat = node.block.stats[i]
    if not stat:is(ast.typed.stat.Var) then
      report_fail(stat, "loop optimization failed: preamble statement is not a variable")
      return
    end
    if not analyze_is_side_effect_free(loop_cx, stat) then
      if not (i == #node.block.stats - 1 and
              stat.value and
              stat.value:is(ast.typed.expr.Call)) then
        report_fail(stat, "loop optimization failed: preamble statement is not side-effect free")
        return
      else
        call_stat = stat
      end
    end

    if call_stat == nil then
      if stat.value and not analyze_is_loop_invariant(loop_cx, stat.value) then
        loop_cx:add_loop_variable(stat.symbol)
        loop_vars:insert(stat)
        -- DELETE ME
        preamble:insert(stat)
      else
        preamble:insert(stat)
      end
    end
  end

  local body = node.block.stats[#node.block.stats]
  local call
  local reduce_lhs, reduce_op = false, false
  if call_stat ~= nil then
    if body:is(ast.typed.stat.Reduce) and
      body.rhs:is(ast.typed.expr.ID) and
      call_stat.symbol == body.rhs.value
    then
      call = call_stat.value
      reduce_lhs = body.lhs
      reduce_op = body.op
    else
      report_fail(call_stat, "loop optimization failed: preamble statement is not side-effect free")
      return
    end
  else
    if body:is(ast.typed.stat.Expr) and
      (body.expr:is(ast.typed.expr.Call) or
       body.expr:is(ast.typed.expr.Fill))
    then
      call = body.expr
    elseif body:is(ast.typed.stat.Reduce) and
      body.rhs:is(ast.typed.expr.Call)
    then
      call = body.rhs
      reduce_lhs = body.lhs
      reduce_op = body.op
    else
      report_fail(body, "loop optimization failed: body is not a function call")
      return
    end
  end

  if call:is(ast.typed.expr.Call) then
    if not std.is_task(call.fn.value) then
      report_fail(call, "loop optimization failed: function is not a task")
      return
    end
  end

  if #call.conditions > 0 then
    report_fail(call, "FIXME: handle analysis of ad-hoc conditions")
    return
  end

  if reduce_lhs then
    local reduce_as_type = std.as_read(call.expr_type)
    if not std.reduction_op_ids[reduce_op][reduce_as_type] then
      report_fail(body, "loop optimization failed: reduction over " .. tostring(reduce_op) .. " " .. tostring(reduce_as_type) .. " not supported")
    end

    if not analyze_is_side_effect_free(loop_cx, reduce_lhs) then
      report_fail(body, "loop optimization failed: reduction is not side-effect free")
    end
  end

  -- Perform static dependence analysis on the loop body to make sure
  -- that the loop is safe to run in parallel. This analysis proceeds
  -- by induction on arguments.
  --
  -- For each argument:
  --
  --  0. Determine whether the argument is provably side-effect
  --     free. (Technically, what this actually does is prove that any
  --     side-effects are non-interfering with the task call itself
  --     and therefore can be split out from the index launch.)
  --
  --  1. Determine whether the argument is provably loop-invariant or
  --     provably "loop-variant" (i.e., a simple function of the loop
  --     index). This is important because index space task launches
  --     are restricted in the forms of region (and index space)
  --     requirements they can accept. All regions (and index spaces)
  --     must be one of:
  --
  --      a. Provably loop-invariant.
  --      b. Provably projectable (i.e. can be expressed as a
  --         projection functor from the partition and index), with
  --         simple indexing which can be analyzed by the optimizer.
  --      c. (Not yet implemented.) Neither, but (i) the region has no
  --         privileges, and (ii) it is provably a subregion of one of
  --         the other region arguments to the task (which must
  --         satisfy either (a) or (b)).
  --
  --  2. For region-typed arguments, compare for non-interference
  --     against previous arguments. Regions must be provably
  --     non-interfering with all previous arguments to pass this
  --     analysis.
  --
  --  3. For region-typed arguments, compare for non-interference
  --     against itself. This means that any arguments that are not
  --     provably loop-variant must be read-only (or reductions,
  --     atomic, simultaneous, etc.). Loop-variant arguments can
  --     additionally prove non-interference by demonstrating that
  --     they come from a disjoint partition, as long as indexing into
  --     said partition is provably disjoint.

  local args_provably = ast.IndexLaunchArgsProvably {
    invariant = terralib.newlist(),
    projectable = terralib.newlist(),
  }

  local free_vars = terralib.newlist()

  -- Perform a simpler analysis if the expression is not a task launch
  if not call:is(ast.typed.expr.Call) then
    if call:is(ast.typed.expr.Fill) then
      if #preamble > 0 or #loop_vars > 0 then
        report_fail(call, "loop optimization failed: fill must not have any preamble statement")
      end

      if not analyze_is_side_effect_free(loop_cx, call.value) then
        report_fail(call.value, "loop optimization failed: fill value" ..
            " is not side-effect free")
        return
      end

      if not analyze_is_loop_invariant(loop_cx, call.value) then
        report_fail(call.value, "loop optimization failed: fill value" ..
            " is not provably invariant")
        return
      end

      local projection = call.dst.region
      if not analyze_is_projectable(loop_cx, projection) then
        report_fail(call, "loop optimization failed: fill target" ..
            " is not provably projectable")
        return
      end

      local partition_type = std.as_read(projection.value.expr_type)
      if not (partition_type and partition_type:is_disjoint() and
         analyze_index_noninterference_self(arg.index, cx, loop_vars))
         -- affine_helper.analyze_index_noninterference_self(cx.loop_index, arg.index, nil))
      then
        report_fail(call, "loop optimization failed: fill target" ..
            " interferes with itself")
        return
      end

      args_provably.invariant:insert(false)
      args_provably.projectable:insert(true)
    else
      -- TODO: Add index copies
      assert(false)
    end

  else
    local task = call.fn.value
    local param_types = task:get_type().parameters
    local args = call.args
    local regions_previously_used = terralib.newlist()
    local mapping = {}
    for i, arg in ipairs(args) do
      if not analyze_is_side_effect_free(loop_cx, arg) then
        report_fail(call, "loop optimization failed: argument " .. tostring(i) .. " is not side-effect free")
        return
      end

      loop_cx.free_variables = terralib.newlist()
      local arg_invariant = analyze_is_loop_invariant(loop_cx, arg)
      free_vars[i] = loop_cx.free_variables

      local arg_projectable = false
      local partition_type

      local arg_type = std.as_read(arg.expr_type)
      -- XXX: This will break again if arg isn't unique for each argument,
      --      which can happen when de-duplicating AST nodes.
      assert(mapping[arg] == nil)
      mapping[arg] = param_types[i]
      -- Tests for conformance to index launch requirements.
      if std.is_region(arg_type) then
        if analyze_is_projectable(loop_cx, arg) then
          partition_type = std.as_read(arg.value.expr_type)
          arg_projectable = true
        end

        if not (arg_projectable or arg_invariant) then
          report_fail(call, "loop optimization failed: argument " .. tostring(i) ..
              " is not provably projectable or invariant")
          return
        end
      end

      if std.is_phase_barrier(arg_type) then
        -- Phase barriers must be invariant, or must not be used as an arrival/wait.
        if not arg_invariant then
          for _, variables in pairs(task:get_conditions()) do
            if variables[i] then
              report_fail(call, "loop optimization failed: argument " .. tostring(i) ..
                  " is not provably invariant")
              return
            end
          end
        end
      end

      if std.is_list(arg_type) and arg_type:is_list_of_regions() then
        -- FIXME: Deoptimize lists of regions for the moment. Lists
        -- would have to be (at a minimum) invariant though other
        -- restrictions may apply.
        report_fail(call, "loop optimization failed: argument " .. tostring(i) .. " is a list of regions")
        return
      end

      -- Tests for non-interference.
      if std.is_region(arg_type) then
        do
          local passed, failure_i = analyze_noninterference_previous(
            loop_cx, task, arg, regions_previously_used, mapping)
          if not passed then
            report_fail(call, "loop optimization failed: argument " .. tostring(i) ..
                " interferes with argument " .. tostring(failure_i))
            return
          end
        end

        do
          local passed = analyze_noninterference_self(
            loop_cx, task, arg, partition_type, mapping, loop_vars)
          if not passed then
            report_fail(call, "loop optimization failed: argument " .. tostring(i) ..
                " interferes with itself")
            return
          end
        end
      end

      args_provably.invariant[i] = arg_invariant
      args_provably.projectable[i] = arg_projectable

      regions_previously_used[i] = nil
      if std.is_region(arg_type) then
        regions_previously_used[i] = arg
      end
    end
  end

  report_pass("loop optimization succeeded")
  return {
    preamble = preamble,
    call = call,
    reduce_lhs = reduce_lhs,
    reduce_op = reduce_op,
    args_provably = args_provably,
    free_variables = free_vars,
    loop_variables = loop_vars
  }
end

function optimize_index_launch.stat_for_num(cx, node)
  local report_pass = ignore
  local report_fail = report.info
  if node.annotations.index_launch:is(ast.annotation.Demand) then
    report_pass = ignore
    report_fail = report.error
  end

  if node.annotations.index_launch:is(ast.annotation.Forbid) then
    return node
  end

  if node.values[3] and not (
    node.values[3]:is(ast.typed.expr.Constant) and
    node.values[3].value == 1)
  then
    report_fail(node, "loop optimization failed: stride not equal to 1")
    return node
  end

  local body = optimize_loop_body(cx, node, report_pass, report_fail)
  if not body then
    return node {
      block = optimize_index_launches.block(cx, node.block),
    }
  end

  return ast.typed.stat.IndexLaunchNum {
    symbol = node.symbol,
    values = node.values,
    preamble = body.preamble,
    call = body.call,
    reduce_lhs = body.reduce_lhs,
    reduce_op = body.reduce_op,
    args_provably = body.args_provably,
    free_vars = body.free_variables,
    loop_vars = body.loop_variables,
    annotations = node.annotations,
    span = node.span,
  }
end

function optimize_index_launch.stat_for_list(cx, node)
  local report_pass = ignore
  local report_fail = report.info
  if node.annotations.index_launch:is(ast.annotation.Demand) then
    report_pass = ignore
    report_fail = report.error
  end

  if node.annotations.index_launch:is(ast.annotation.Forbid) then
    return node
  end

  local value_type = std.as_read(node.value.expr_type)
  if not (std.is_rect_type(value_type) or
          std.is_ispace(value_type) or
          std.is_region(value_type))
  then
    report_fail(node, "loop optimization failed: domain is not a ispace or region")
    return node
  end

  local body = optimize_loop_body(cx, node, report_pass, report_fail)
  if not body then
    return node {
      block = optimize_index_launches.block(cx, node.block),
    }
  end

  return ast.typed.stat.IndexLaunchList {
    symbol = node.symbol,
    value = node.value,
    preamble = body.preamble,
    call = body.call,
    reduce_lhs = body.reduce_lhs,
    reduce_op = body.reduce_op,
    args_provably = body.args_provably,
    free_vars = body.free_variables,
    loop_vars = body.loop_variables,
    annotations = node.annotations,
    span = node.span,
  }
end

function optimize_index_launches.stat_block(cx, node)
  return node {
    block = optimize_index_launches.block(cx, node.block),
  }
end

function optimize_index_launches.stat_if(cx, node)
  local then_block = optimize_index_launches.block(cx, node.then_block)
  local elseif_blocks = node.elseif_blocks:map(function(elseif_block)
    return optimize_index_launches.stat(cx, elseif_block)
  end)
  local else_block = optimize_index_launches.block(cx, node.else_block)
  return node {
    then_block = then_block,
    elseif_blocks = elseif_blocks,
    else_block = else_block,
  }
end

function optimize_index_launches.stat_elseif(cx, node)
  local block = optimize_index_launches.block(cx, node.block)
  return node { block = block }
end

local function do_nothing(cx, node) return node end

local optimize_index_launches_stat_table = {
  [ast.typed.stat.ForNum]    = optimize_index_launch.stat_for_num,
  [ast.typed.stat.ForList]   = optimize_index_launch.stat_for_list,

  [ast.typed.stat.While]     = optimize_index_launches.stat_block,
  [ast.typed.stat.Repeat]    = optimize_index_launches.stat_block,
  [ast.typed.stat.Block]     = optimize_index_launches.stat_block,
  [ast.typed.stat.MustEpoch] = optimize_index_launches.stat_block,
  [ast.typed.stat.While]     = optimize_index_launches.stat_block,
  [ast.typed.stat.If]        = optimize_index_launches.stat_if,
  [ast.typed.stat.Elseif]    = optimize_index_launches.stat_elseif,
  [ast.typed.stat]           = do_nothing,
}

local optimize_index_launches_stat = ast.make_single_dispatch(
  optimize_index_launches_stat_table,
  {})

function optimize_index_launches.stat(cx, node)
  return optimize_index_launches_stat(cx)(node)
end

function optimize_index_launches.block(cx, node)
  return node {
    stats = node.stats:map(function(stat)
      return optimize_index_launches.stat(cx, stat)
    end)
  }
end

function optimize_index_launches.top_task(cx, node)
  if not node.body then return node end

  local cx = cx:new_task_scope(node.prototype:get_constraints())
  local body = optimize_index_launches.block(cx, node.body)

  return node { body = body }
end

function optimize_index_launches.top(cx, node)
  if node:is(ast.typed.top.Task) and
     not node.config_options.leaf
  then
    return optimize_index_launches.top_task(cx, node)

  else
    return node
  end
end

function optimize_index_launches.entry(node)
  local cx = context.new_global_scope({})
  return optimize_index_launches.top(cx, node)
end

optimize_index_launches.pass_name = "optimize_index_launches"

return optimize_index_launches
