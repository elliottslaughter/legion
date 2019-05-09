#!/usr/bin/env python

# Copyright 2019 Stanford University
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

from __future__ import absolute_import, division, print_function, unicode_literals

import cffi
try:
    import cPickle as pickle
except ImportError:
    import pickle
import collections
import itertools
import math
import numpy
import os
import re
import subprocess
import sys
import threading
import weakref

# Python 3.x compatibility:
try:
    long # Python 2
except NameError:
    long = int  # Python 3

try:
    xrange # Python 2
except NameError:
    xrange = range # Python 3

try:
    imap = itertools.imap # Python 2
except:
    imap = map # Python 3

try:
    zip_longest = itertools.izip_longest # Python 2
except:
    zip_longest = itertools.zip_longest # Python 3

_pickle_version = pickle.HIGHEST_PROTOCOL # Use latest Pickle protocol

_max_dim = int(os.environ.get('MAX_DIM', 3))

def find_legion_header():
    def try_prefix(prefix_dir):
        legion_h_path = os.path.join(prefix_dir, 'legion.h')
        if os.path.exists(legion_h_path):
            return prefix_dir, legion_h_path

    # For in-source builds, find the header relative to the bindings
    root_dir = os.path.dirname(os.path.dirname(os.path.dirname(os.path.realpath(__file__))))
    runtime_dir = os.path.join(root_dir, 'runtime')
    result = try_prefix(runtime_dir)
    if result:
        return result

    # If this was installed to a non-standard prefix, we might be able
    # to guess from the directory structures
    if os.path.basename(root_dir) == 'lib':
        include_dir = os.path.join(os.path.dirname(root_dir), 'include')
        result = try_prefix(include_dir)
        if result:
            return result

    # Otherwise we have to hope that Legion is installed in a standard location
    result = try_prefix('/usr/include')
    if result:
        return result

    result = try_prefix('/usr/local/include')
    if result:
        return result

    raise Exception('Unable to locate legion.h header file')

prefix_dir, legion_h_path = find_legion_header()
header = subprocess.check_output(['gcc', '-I', prefix_dir, '-DLEGION_MAX_DIM=%s' % _max_dim, '-DREALM_MAX_DIM=%s' % _max_dim, '-E', '-P', legion_h_path]).decode('utf-8')

# Hack: Fix for Ubuntu 16.04 versions of standard library headers:
header = re.sub(r'typedef struct {.+?} max_align_t;', '', header, flags=re.DOTALL)

ffi = cffi.FFI()
ffi.cdef(header)
c = ffi.dlopen(None)

# Can't seem to pull this out of the header, so reproduce it here.
AUTO_GENERATE_ID = -1

# Note: don't use __file__ here, it may return either .py or .pyc and cause
# non-deterministic failures.
library_name = "legion.py"
max_legion_python_tasks = 1000000
next_legion_task_id = c.legion_runtime_generate_library_task_ids(
                        c.legion_runtime_get_runtime(),
                        library_name.encode('utf-8'),
                        max_legion_python_tasks)
max_legion_task_id = next_legion_task_id + max_legion_python_tasks

# Returns true if this module is running inside of a Legion
# executable. If false, then other Legion functionality should not be
# expected to work.
def inside_legion_executable():
    try:
        c.legion_get_current_time_in_micros()
    except AttributeError:
        return False
    else:
        return True

def input_args(filter_runtime_options=False):
    raw_args = c.legion_runtime_get_input_args()

    args = []
    for i in range(raw_args.argc):
        args.append(ffi.string(raw_args.argv[i]).decode('utf-8'))

    if filter_runtime_options:
        i = 1 # Skip program name

        prefixes = ['-lg:', '-hl:', '-realm:', '-ll:', '-cuda:', '-numa:',
                    '-dm:', '-bishop:']
        while i < len(args):
            match = False
            for prefix in prefixes:
                if args[i].startswith(prefix):
                    match = True
                    break
            if args[i] == '-level':
                match = True
            if args[i] == '-logfile':
                match = True
            if match:
                args.pop(i)
                args.pop(i) # Assume that every option has an argument
                continue
            i += 1
    return args

# The Legion context is stored in thread-local storage. This assumes
# that the Python processor maintains the invariant that every task
# corresponds to one and only one thread.
_my = threading.local()

global_task_registration_barrier = None

class Context(object):
    __slots__ = ['context_root', 'context', 'runtime_root', 'runtime',
                 'task_root', 'task', 'regions',
                 'owned_objects', 'current_launch']
    def __init__(self, context_root, runtime_root, task_root, regions):
        self.context_root = context_root
        self.context = self.context_root[0]
        self.runtime_root = runtime_root
        self.runtime = self.runtime_root[0]
        self.task_root = task_root
        self.task = self.task_root[0]
        self.regions = regions
        self.owned_objects = []
        self.current_launch = None
    def track_object(self, obj):
        self.owned_objects.append(weakref.ref(obj))
    def begin_launch(self, launch):
        assert self.current_launch == None
        self.current_launch = launch
    def end_launch(self, launch):
        assert self.current_launch == launch
        self.current_launch = None

# Hack: Can't pickle static methods.
def _DomainPoint_unpickle(values):
    return DomainPoint.create(values)

class DomainPoint(object):
    __slots__ = ['handle']
    def __init__(self, handle, take_ownership=False):
        # Important: Copy handle. Do NOT assume ownership unless explicitly told.
        if take_ownership:
            self.handle = handle
        else:
            self.handle = ffi.new('legion_domain_t *', handle)

    def __reduce__(self):
        return (_DomainPoint_unpickle,
                ([self.handle[0].point_data[i] for i in xrange(self.handle[0].dim)],))

    def __int__(self):
        assert self.handle[0].dim == 1
        return self.handle[0].point_data[0]

    def __index__(self):
        assert self.handle[0].dim == 1
        return self.handle[0].point_data[0]

    def __getitem__(self, i):
        assert 0 <= i < self.handle[0].dim
        return self.handle[0].point_data[i]

    def __eq__(self, other):
        if not isinstance(other, DomainPoint):
            return NotImplemented
        if self.handle[0].dim != other.handle[0].dim:
            return False
        for i in xrange(self.handle[0].dim):
            if self.handle[0].point_data[i] != other.handle[0].point_data[i]:
                return False
        return True

    def __str__(self):
        dim = self.handle[0].dim
        if dim == 1:
            return str(self.handle[0].point_data[0])
        return '({})'.format(
            ', '.join(str(self.handle[0].point_data[i]) for i in xrange(dim)))

    def __repr__(self):
        dim = self.handle[0].dim
        return 'DomainPoint({})'.format(
            ', '.join(str(self.handle[0].point_data[i]) for i in xrange(dim)))

    @staticmethod
    def create(values):
        try:
            len(values)
        except TypeError:
            values = [values]
        assert 1 <= len(values) <= _max_dim
        handle = ffi.new('legion_domain_point_t *')
        handle[0].dim = len(values)
        for i, value in enumerate(values):
            handle[0].point_data[i] = value
        return DomainPoint(handle, take_ownership=True)

    @staticmethod
    def create_from_index(value):
        assert(isinstance(value, _IndexValue))
        handle = ffi.new('legion_domain_point_t *')
        handle[0].dim = 1
        handle[0].point_data[0] = int(value)
        return DomainPoint(handle, take_ownership=True)

    def raw_value(self):
        return self.handle[0]

class Domain(object):
    __slots__ = ['handle']
    def __init__(self, handle):
        # Important: Copy handle. Do NOT assume ownership.
        self.handle = ffi.new('legion_domain_t *', handle)

    @property
    def volume(self):
        return c.legion_domain_get_volume(self.handle[0])

    @staticmethod
    def create(extent, start=None):
        try:
            len(extent)
        except TypeError:
            extent = [extent]
        if start is not None:
            try:
                len(start)
            except TypeError:
                start = [start]
            assert len(start) == len(extent)
        else:
            start = [0 for _ in extent]
        assert 1 <= len(extent) <= _max_dim
        rect = ffi.new('legion_rect_{}d_t *'.format(len(extent)))
        for i in xrange(len(extent)):
            rect[0].lo.x[i] = start[i]
            rect[0].hi.x[i] = start[i] + extent[i] - 1
        return Domain(getattr(c, 'legion_domain_from_rect_{}d'.format(len(extent)))(rect[0]))

    def __iter__(self):
        dim = self.handle[0].dim
        return imap(
            DomainPoint.create,
            itertools.product(
                *[xrange(
                    self.handle[0].rect_data[i],
                    self.handle[0].rect_data[i+dim] + 1)
                  for i in xrange(dim)]))

    def raw_value(self):
        return self.handle[0]

class Future(object):
    __slots__ = ['handle', 'value_type', 'argument_number']
    def __init__(self, value, value_type=None, argument_number=None):
        if value is None:
            self.handle = None
        elif isinstance(value, Future):
            value.resolve_handle()
            self.handle = c.legion_future_copy(value.handle)
            if value_type is None:
                value_type = value.value_type
        elif value_type is not None:
            if value_type.size > 0:
                value_ptr = ffi.new(ffi.getctype(value_type.cffi_type, '*'), value)
            else:
                value_ptr = ffi.NULL
            value_size = value_type.size
            self.handle = c.legion_future_from_untyped_pointer(_my.ctx.runtime, value_ptr, value_size)
        else:
            value_str = pickle.dumps(value, protocol=_pickle_version)
            value_size = len(value_str)
            value_ptr = ffi.new('char[]', value_size)
            ffi.buffer(value_ptr, value_size)[:] = value_str
            self.handle = c.legion_future_from_untyped_pointer(_my.ctx.runtime, value_ptr, value_size)

        self.value_type = value_type
        self.argument_number = argument_number

    @staticmethod
    def from_cdata(value, *args, **kwargs):
        result = Future(None, *args, **kwargs)
        result.handle = c.legion_future_copy(value)
        return result

    @staticmethod
    def from_buffer(value, *args, **kwargs):
        result = Future(None, *args, **kwargs)
        result.handle = c.legion_future_from_untyped_pointer(_my.ctx.runtime, ffi.from_buffer(value), len(value))
        return result

    def __del__(self):
        if self.handle is not None:
            c.legion_future_destroy(self.handle)

    def __reduce__(self):
        if self.argument_number is None:
            raise Exception('Cannot pickle a Future except when used as a task argument')
        return (Future, (None, self.value_type, self.argument_number))

    def resolve_handle(self):
        if self.handle is None and self.argument_number is not None:
            self.handle = c.legion_future_copy(
                c.legion_task_get_future(_my.ctx.task, self.argument_number))

    def get(self):
        self.resolve_handle()

        if self.handle is None:
            return
        if self.value_type is None:
            value_ptr = c.legion_future_get_untyped_pointer(self.handle)
            value_size = c.legion_future_get_untyped_size(self.handle)
            assert value_size > 0
            value_str = ffi.unpack(ffi.cast('char *', value_ptr), value_size)
            value = pickle.loads(value_str)
            return value
        elif self.value_type.size == 0:
            c.legion_future_get_void_result(self.handle)
        else:
            expected_size = ffi.sizeof(self.value_type.cffi_type)

            value_ptr = c.legion_future_get_untyped_pointer(self.handle)
            value_size = c.legion_future_get_untyped_size(self.handle)
            assert value_size == expected_size
            value = ffi.cast(ffi.getctype(self.value_type.cffi_type, '*'), value_ptr)[0]
            return value

    def get_buffer(self):
        self.resolve_handle()

        if self.handle is None:
            return
        value_ptr = c.legion_future_get_untyped_pointer(self.handle)
        value_size = c.legion_future_get_untyped_size(self.handle)
        return ffi.buffer(value_ptr, value_size)

class FutureMap(object):
    __slots__ = ['handle', 'value_type']
    def __init__(self, handle, value_type=None):
        self.handle = c.legion_future_map_copy(handle)
        self.value_type = value_type

    def __del__(self):
        c.legion_future_map_destroy(self.handle)

    def __getitem__(self, point):
        if not isinstance(point, DomainPoint):
            point = DomainPoint.create(point)
        return Future.from_cdata(
            c.legion_future_map_get_future(self.handle, point.raw_value()),
            value_type=self.value_type)

class Type(object):
    __slots__ = ['numpy_type', 'cffi_type', 'size']

    def __init__(self, numpy_type, cffi_type):
        assert (numpy_type is None) == (cffi_type is None)
        self.numpy_type = numpy_type
        self.cffi_type = cffi_type
        self.size = numpy.dtype(numpy_type).itemsize if numpy_type is not None else 0

    def __reduce__(self):
        return (Type, (self.numpy_type, self.cffi_type))

# Pre-defined Types
void = Type(None, None)
float16 = Type(numpy.float16, 'short float')
float32 = Type(numpy.float32, 'float')
float64 = Type(numpy.float64, 'double')
int8 = Type(numpy.int8, 'int8_t')
int16 = Type(numpy.int16, 'int16_t')
int32 = Type(numpy.int32, 'int32_t')
int64 = Type(numpy.int64, 'int64_t')
uint8 = Type(numpy.uint8, 'uint8_t')
uint16 = Type(numpy.uint16, 'uint16_t')
uint32 = Type(numpy.uint32, 'uint32_t')
uint64 = Type(numpy.uint64, 'uint64_t')

class Privilege(object):
    __slots__ = ['read', 'write', 'discard']

    def __init__(self, read=False, write=False, discard=False):
        self.read = read
        self.write = write
        self.discard = discard

    def _fields(self):
        return (self.read, self.write, self.discard)

    def __eq__(self, other):
        return isinstance(other, Privilege) and self._fields() == other._fields()

    def __cmp__(self, other):
        assert isinstance(other, Privilege)
        return self._fields().__cmp__(other._fields())

    def __hash__(self):
        return hash(self._fields())

    def __call__(self, fields):
        return PrivilegeFields(self, fields)

    def _legion_privilege(self):
        bits = 0
        if self.discard:
            assert self.write
            bits |= 2 # WRITE_DISCARD
        else:
            if self.write: bits = 7 # READ_WRITE
            elif self.read: bits = 1 # READ_ONLY
        return bits

class PrivilegeFields(Privilege):
    __slots__ = ['read', 'write', 'discard', 'fields']

    def __init__(self, privilege, fields):
        Privilege.__init__(self, privilege.read, privilege.write, privilege.discard)
        self.fields = fields

# Pre-defined Privileges
N = Privilege()
R = Privilege(read=True)
RO = Privilege(read=True)
RW = Privilege(read=True, write=True)
WD = Privilege(write=True, discard=True)

# Hack: Can't pickle static methods.
def _Ispace_unpickle(ispace_tid, ispace_id, ispace_type_tag, owned):
    handle = ffi.new('legion_index_space_t *')
    handle[0].tid = ispace_tid
    handle[0].id = ispace_id
    handle[0].type_tag = ispace_type_tag
    return Ispace(handle[0], owned=owned)

class Ispace(object):
    __slots__ = [
        'handle', 'owned', 'escaped',
        '__weakref__', # allow weak references
    ]

    def __init__(self, handle, owned=False):
        # Important: Copy handle. Do NOT assume ownership.
        self.handle = ffi.new('legion_index_space_t *', handle)
        self.owned = owned
        self.escaped = False

        if self.owned:
            _my.ctx.track_object(self)

    def __del__(self):
        if self.owned and not self.escaped:
            self.destroy()

    def __reduce__(self):
        return (_Ispace_unpickle,
                (self.handle[0].tid,
                 self.handle[0].id,
                 self.handle[0].type_tag,
                 self.owned and self.escaped))

    def __iter__(self):
        return self.domain.__iter__()

    @property
    def domain(self):
        domain = c.legion_index_space_get_domain(_my.ctx.runtime, self.handle[0])
        return Domain(domain)

    @property
    def volume(self):
        return self.domain.volume

    @staticmethod
    def create(extent, start=None):
        domain = Domain.create(extent, start=start).raw_value()
        handle = c.legion_index_space_create_domain(_my.ctx.runtime, _my.ctx.context, domain)
        return Ispace(handle, owned=True)

    def destroy(self):
        assert self.owned and not self.escaped

        # This is not something you want to have happen in a
        # destructor, since fspaces may outlive the lifetime of the handle.
        c.legion_index_space_destroy(
            _my.ctx.runtime, _my.ctx.context, self.handle[0])
        # Clear out references. Technically unnecessary but avoids abuse.
        del self.handle

# Hack: Can't pickle static methods.
def _Fspace_unpickle(fspace_id, field_ids, field_types, owned):
    handle = ffi.new('legion_field_space_t *')
    handle[0].id = fspace_id
    return Fspace(handle[0], field_ids, field_types, owned=owned)

class Fspace(object):
    __slots__ = [
        'handle', 'field_ids', 'field_types',
        'owned', 'escaped',
        '__weakref__', # allow weak references
    ]

    def __init__(self, handle, field_ids, field_types, owned=False):
        # Important: Copy handle. Do NOT assume ownership.
        self.handle = ffi.new('legion_field_space_t *', handle)
        self.field_ids = field_ids
        self.field_types = field_types
        self.owned = owned
        self.escaped = False

        if owned:
            _my.ctx.track_object(self)

    def __del__(self):
        if self.owned and not self.escaped:
            self.destroy()

    def __reduce__(self):
        return (_Fspace_unpickle,
                (self.handle[0].id,
                 self.field_ids,
                 self.field_types,
                 self.owned and self.escaped))

    @staticmethod
    def create(fields):
        handle = c.legion_field_space_create(_my.ctx.runtime, _my.ctx.context)
        alloc = c.legion_field_allocator_create(
            _my.ctx.runtime, _my.ctx.context, handle)
        field_ids = collections.OrderedDict()
        field_types = collections.OrderedDict()
        for field_name, field_entry in fields.items():
            try:
                field_type, field_id = field_entry
            except TypeError:
                field_type = field_entry
                field_id = ffi.cast('legion_field_id_t', AUTO_GENERATE_ID)
            field_id = c.legion_field_allocator_allocate_field(
                alloc, field_type.size, field_id)
            c.legion_field_id_attach_name(
                _my.ctx.runtime, handle, field_id, field_name.encode('utf-8'), False)
            field_ids[field_name] = field_id
            field_types[field_name] = field_type
        c.legion_field_allocator_destroy(alloc)
        return Fspace(handle, field_ids, field_types, owned=True)

    def destroy(self):
        assert self.owned and not self.escaped

        # This is not something you want to have happen in a
        # destructor, since fspaces may outlive the lifetime of the handle.
        c.legion_field_space_destroy(
            _my.ctx.runtime, _my.ctx.context, self.handle[0])
        # Clear out references. Technically unnecessary but avoids abuse.
        del self.handle
        del self.field_ids
        del self.field_types

# Hack: Can't pickle static methods.
def _Region_unpickle(tree_id, ispace, fspace, owned):
    handle = ffi.new('legion_logical_region_t *')
    handle[0].tree_id = tree_id
    handle[0].index_space = ispace.handle[0]
    handle[0].field_space = fspace.handle[0]

    return Region(handle[0], ispace, fspace, owned=owned)

class Region(object):
    __slots__ = [
        'handle', 'ispace', 'fspace', 'parent',
        'instances', 'privileges', 'instance_wrappers',
        'owned', 'escaped',
        '__weakref__', # allow weak references
    ]

    # Make this speak the Type interface
    numpy_type = None
    cffi_type = 'legion_logical_region_t'
    size = ffi.sizeof(cffi_type)

    def __init__(self, handle, ispace, fspace, parent=None, owned=False):
        # Important: Copy handle. Do NOT assume ownership.
        self.handle = ffi.new('legion_logical_region_t *', handle)
        self.ispace = ispace
        self.fspace = fspace
        self.parent = parent
        self.owned = owned
        self.escaped = False
        self.instances = {}
        self.privileges = {}
        self.instance_wrappers = {}

        if owned:
            _my.ctx.track_object(self)
            for field_name in fspace.field_ids.keys():
                self._set_privilege(field_name, RW)

    def __del__(self):
        if self.owned and not self.escaped:
            self.destroy()

    def __reduce__(self):
        return (_Region_unpickle,
                (self.handle[0].tree_id,
                 self.ispace,
                 self.fspace,
                 self.owned and self.escaped))

    @staticmethod
    def create(ispace, fspace):
        if not isinstance(ispace, Ispace):
            ispace = Ispace.create(ispace)
        if not isinstance(fspace, Fspace):
            fspace = Fspace.create(fspace)
        handle = c.legion_logical_region_create(
            _my.ctx.runtime, _my.ctx.context, ispace.handle[0], fspace.handle[0], False)
        return Region(handle, ispace, fspace, owned=True)

    def destroy(self):
        assert self.owned and not self.escaped

        # This is not something you want to have happen in a
        # destructor, since regions may outlive the lifetime of the handle.
        c.legion_logical_region_destroy(
            _my.ctx.runtime, _my.ctx.context, self.handle[0])
        # Clear out references. Technically unnecessary but avoids abuse.
        del self.parent
        del self.instance_wrappers
        del self.instances
        del self.handle
        del self.ispace
        del self.fspace

    def _set_privilege(self, field_name, privilege):
        assert self.parent is None # not supported on subregions
        assert field_name not in self.privileges
        self.privileges[field_name] = privilege

    def _set_instance(self, field_name, instance, privilege=None):
        assert self.parent is None # not supported on subregions
        assert field_name not in self.instances
        self.instances[field_name] = instance
        if privilege is not None:
            self._set_privilege(field_name, privilege)

    def _map_inline(self):
        assert self.parent is None # FIXME: support inline mapping subregions

        fields_by_privilege = collections.defaultdict(set)
        for field_name, privilege in self.privileges.items():
            fields_by_privilege[privilege].add(field_name)
        for privilege, field_names  in fields_by_privilege.items():
            launcher = c.legion_inline_launcher_create_logical_region(
                self.handle[0],
                privilege._legion_privilege(), 0, # EXCLUSIVE
                self.handle[0],
                0, False, 0, 0)
            for field_name in field_names:
                c.legion_inline_launcher_add_field(
                    launcher, self.fspace.field_ids[field_name], True)
            instance = c.legion_inline_launcher_execute(
                _my.ctx.runtime, _my.ctx.context, launcher)
            for field_name in field_names:
                self._set_instance(field_name, instance)

    def __getattr__(self, field_name):
        if field_name in self.fspace.field_ids:
            if field_name not in self.instances:
                if self.privileges[field_name] is None:
                    raise Exception('Invalid attempt to access field "%s" without privileges' % field_name)
                self._map_inline()
            if field_name not in self.instance_wrappers:
                self.instance_wrappers[field_name] = RegionField(
                    self, field_name)
            return self.instance_wrappers[field_name]
        else:
            raise AttributeError()

class RegionField(numpy.ndarray):
    # NumPy requires us to implement __new__ for subclasses of ndarray:
    # https://docs.scipy.org/doc/numpy/user/basics.subclassing.html
    def __new__(cls, region, field_name):
        accessor = RegionField._get_accessor(region, field_name)
        initializer = RegionField._get_array_initializer(region, field_name, accessor)
        obj = numpy.asarray(initializer).view(cls)

        obj.accessor = accessor
        return obj

    @staticmethod
    def _get_accessor(region, field_name):
        # Note: the accessor needs to be kept alive, to make sure to
        # save the result of this function in an instance variable.
        instance = region.instances[field_name]
        domain = c.legion_index_space_get_domain(
            _my.ctx.runtime, region.ispace.handle[0])
        dim = domain.dim
        get_accessor = getattr(c, 'legion_physical_region_get_field_accessor_array_{}d'.format(dim))
        return get_accessor(instance, region.fspace.field_ids[field_name])

    @staticmethod
    def _get_base_and_stride(region, field_name, accessor):
        domain = c.legion_index_space_get_domain(
            _my.ctx.runtime, region.ispace.handle[0])
        dim = domain.dim
        rect = getattr(c, 'legion_domain_get_rect_{}d'.format(dim))(domain)
        subrect = ffi.new('legion_rect_{}d_t *'.format(dim))
        offsets = ffi.new('legion_byte_offset_t[]', dim)

        base_ptr = getattr(c, 'legion_accessor_array_{}d_raw_rect_ptr'.format(dim))(
            accessor, rect, subrect, offsets)
        assert base_ptr
        for i in xrange(dim):
            assert subrect[0].lo.x[i] == rect.lo.x[i]
            assert subrect[0].hi.x[i] == rect.hi.x[i]
        assert offsets[0].offset == region.fspace.field_types[field_name].size

        shape = tuple(rect.hi.x[i] - rect.lo.x[i] + 1 for i in xrange(dim))
        strides = tuple(offsets[i].offset for i in xrange(dim))

        return base_ptr, shape, strides

    @staticmethod
    def _get_array_initializer(region, field_name, accessor):
        base_ptr, shape, strides = RegionField._get_base_and_stride(
            region, field_name, accessor)
        field_type = region.fspace.field_types[field_name]

        # Numpy doesn't know about CFFI pointers, so we have to cast
        # this to a Python long before we can hand it off to Numpy.
        base_ptr = long(ffi.cast("size_t", base_ptr))

        return _RegionNdarray(shape, field_type, base_ptr, strides, False)

# This is a dummy object that is only used as an initializer for the
# RegionField object above. It is thrown away as soon as the
# RegionField is constructed.
class _RegionNdarray(object):
    __slots__ = ['__array_interface__']
    def __init__(self, shape, field_type, base_ptr, strides, read_only):
        # See: https://docs.scipy.org/doc/numpy/reference/arrays.interface.html
        self.__array_interface__ = {
            'version': 3,
            'shape': shape,
            'typestr': numpy.dtype(field_type.numpy_type).str,
            'data': (base_ptr, read_only),
            'strides': strides,
        }

def fill(region, field_name, value):
    assert(isinstance(region, Region))
    field_id = region.fspace.field_ids[field_name]
    field_type = region.fspace.field_types[field_name]
    raw_value = ffi.new('{} *'.format(field_type.cffi_type), value)
    c.legion_runtime_fill_field(
        _my.ctx.runtime, _my.ctx.context,
        region.handle[0], region.parent.handle[0] if region.parent is not None else region.handle[0],
        field_id, raw_value, field_type.size,
        c.legion_predicate_true())

# Hack: Can't pickle static methods.
def _Ipartition_unpickle(id, parent, color_space):
    handle = ffi.new('legion_index_partition_t *')
    handle[0].id = id
    handle[0].tid = parent.handle[0].tid
    handle[0].type_tag = parent.handle[0].type_tag

    return Ipartition(handle[0], parent, color_space)

class Ipartition(object):
    __slots__ = ['handle', 'parent', 'color_space']

    # Make this speak the Type interface
    numpy_type = None
    cffi_type = 'legion_index_partition_t'
    size = ffi.sizeof(cffi_type)

    def __init__(self, handle, parent, color_space):
        # Important: Copy handle. Do NOT assume ownership.
        self.handle = ffi.new('legion_index_partition_t *', handle)
        self.parent = parent
        self.color_space = color_space

    def __reduce__(self):
        return (_Ipartition_unpickle,
                (self.handle[0].id, self.parent, self.color_space))

    def __getitem__(self, point):
        if not isinstance(point, DomainPoint):
            point = DomainPoint.create(point)
        subspace = c.legion_index_partition_get_index_subspace_domain_point(
            _my.ctx.runtime, self.handle[0], point.raw_value())
        return Ispace(subspace)

    def __iter__(self):
        for point in self.color_space:
            yield self[point]

    @staticmethod
    def create_equal(parent, color_space, granularity=1, color=AUTO_GENERATE_ID):
        assert isinstance(parent, Ispace)
        if not isinstance(color_space, Ispace):
            color_space = Ispace.create(color_space)
        handle = c.legion_index_partition_create_equal(
            _my.ctx.runtime, _my.ctx.context,
            parent.handle[0], color_space.handle[0], granularity, color)
        return Ipartition(handle, parent, color_space)

    def destroy(self):
        # This is not something you want to have happen in a
        # destructor, since partitions may outlive the lifetime of the handle.
        c.legion_index_partition_destroy(
            _my.ctx.runtime, _my.ctx.context, self.handle[0])
        # Clear out references. Technically unnecessary but avoids abuse.
        del self.handle
        del self.parent
        del self.color_space

# Hack: Can't pickle static methods.
def _Partition_unpickle(parent, ipartition):
    handle = ffi.new('legion_logical_partition_t *')
    handle[0].tree_id = parent.handle[0].tree_id
    handle[0].index_partition = ipartition.handle[0]
    handle[0].field_space = parent.fspace.handle[0]

    return Partition(handle[0], parent, ipartition)

class Partition(object):
    __slots__ = ['handle', 'parent', 'ipartition']

    # Make this speak the Type interface
    numpy_type = None
    cffi_type = 'legion_logical_partition_t'
    size = ffi.sizeof(cffi_type)

    def __init__(self, handle, parent, ipartition):
        # Important: Copy handle. Do NOT assume ownership.
        self.handle = ffi.new('legion_logical_partition_t *', handle)
        self.parent = parent
        self.ipartition = ipartition

    def __reduce__(self):
        return (_Partition_unpickle,
                (self.parent,
                 self.ipartition))

    def __getitem__(self, point):
        if not isinstance(point, DomainPoint):
            point = DomainPoint.create(point)
        subspace = self.ipartition[point]
        subregion = c.legion_logical_partition_get_logical_subregion_by_color_domain_point(
            _my.ctx.runtime, self.handle[0], point.raw_value())
        return Region(subregion, subspace, self.parent.fspace,
                      parent=self.parent.parent if self.parent.parent is not None else self.parent)

    def __iter__(self):
        for point in self.color_space:
            yield self[point]

    @property
    def color_space(self):
        return self.ipartition.color_space

    @staticmethod
    def create(parent, ipartition):
        assert isinstance(parent, Region)
        assert isinstance(ipartition, Ipartition)
        handle = c.legion_logical_partition_create(
            _my.ctx.runtime, _my.ctx.context, parent.handle[0], ipartition.handle[0])
        return Partition(handle, parent, ipartition)

    @staticmethod
    def create_equal(parent, color_space, granularity=1, color=AUTO_GENERATE_ID):
        assert isinstance(parent, Region)
        ipartition = Ipartition.create_equal(parent.ispace, color_space, granularity, color)
        return Partition.create(parent, ipartition)

    def destroy(self):
        # This is not something you want to have happen in a
        # destructor, since partitions may outlive the lifetime of the handle.
        c.legion_logical_partition_destroy(
            _my.ctx.runtime, _my.ctx.context, self.handle[0])
        # Clear out references. Technically unnecessary but avoids abuse.
        del self.handle
        del self.parent
        del self.ipartition

def define_regent_argument_struct(task_id, argument_types, privileges, return_type, arguments):
    if argument_types is None:
        raise Exception('Arguments must be typed in extern Regent tasks')

    struct_name = 'task_args_%s' % task_id

    n_fields = int(math.ceil(len(argument_types)/64.))

    fields = ['uint64_t %s[%s];' % ('__map', n_fields)]
    for i, arg_type in enumerate(argument_types):
        arg_name = '__arg_%s' % i
        fields.append('%s %s;' % (arg_type.cffi_type, arg_name))
    for i, arg in enumerate(arguments):
        if isinstance(arg, Region):
            for j, field_type in enumerate(arg.fspace.field_types.values()):
                arg_name = '__arg_%s_field_%s' % (i, j)
                fields.append('legion_field_id_t %s;' % arg_name)

    struct = 'typedef struct %s { %s } %s;' % (struct_name, ' '.join(fields), struct_name)
    ffi.cdef(struct)

    return struct_name

class ExternTask(object):
    __slots__ = ['argument_types', 'privileges', 'return_type',
                 'calling_convention', 'task_id', '_argument_struct']

    def __init__(self, task_id, argument_types=None, privileges=None,
                 return_type=void, calling_convention=None):
        self.argument_types = argument_types
        if privileges is not None:
            privileges = [(x if x is not None else N) for x in privileges]
        self.privileges = privileges
        self.return_type = return_type
        self.calling_convention = calling_convention
        assert isinstance(task_id, int)
        self.task_id = task_id
        self._argument_struct = None

    def argument_struct(self, args):
        if self.calling_convention == 'regent' and self._argument_struct is None:
            self._argument_struct = define_regent_argument_struct(
                self.task_id, self.argument_types, self.privileges, self.return_type, args)
        return self._argument_struct

    def __call__(self, *args):
        return self.spawn_task(*args)

    def spawn_task(self, *args):
        if _my.ctx.current_launch:
            return _my.ctx.current_launch.spawn_task(self, *args)
        return TaskLaunch().spawn_task(self, *args)

def extern_task(**kwargs):
    return ExternTask(**kwargs)

def get_qualname(fn):
    # Python >= 3.3 only
    try:
        return fn.__qualname__.split('.')
    except AttributeError:
        pass

    # Python < 3.3
    try:
        import qualname
        return qualname.qualname(fn).split('.')
    except ImportError:
        pass

    # Hack: Issue error if we're wrapping a class method and failed to
    # get the qualname
    import inspect
    context = [x[0].f_code.co_name for x in inspect.stack()
               if '__module__' in x[0].f_code.co_names and
               inspect.getmodule(x[0].f_code).__name__ != __name__]
    if len(context) > 0:
        raise Exception('To use a task defined in a class, please upgrade to Python >= 3.3 or install qualname (e.g. pip install qualname)')

    return [fn.__name__]

class Task (object):
    __slots__ = ['body', 'privileges', 'return_type',
                 'leaf', 'inner', 'idempotent', 'replicable',
                 'calling_convention', 'argument_struct',
                 'task_id', 'registered']

    def __init__(self, body, privileges=None, return_type=None,
                 leaf=False, inner=False, idempotent=False, replicable=False,
                 register=True, task_id=None, top_level=False):
        self.body = body
        if privileges is not None:
            privileges = [(x if x is not None else N) for x in privileges]
        self.privileges = privileges
        self.return_type = return_type
        self.leaf = bool(leaf)
        self.inner = bool(inner)
        self.idempotent = bool(idempotent)
        self.replicable = bool(replicable)
        self.calling_convention = 'python'
        self.argument_struct = None
        self.task_id = None
        if register:
            self.register(task_id, top_level)

    def __call__(self, *args, **kwargs):
        # Hack: This entrypoint needs to be able to handle both being
        # called in user code (to launch a task) and as the task
        # wrapper when the task itself executes. Unfortunately isn't a
        # good way to disentangle these. Detect if we're in the task
        # wrapper case by checking the number and types of arguments.
        if len(args) == 3 and \
           isinstance(args[0], bytearray) and \
           isinstance(args[1], bytearray) and \
           isinstance(args[2], long):
            return self.execute_task(*args, **kwargs)
        else:
            return self.spawn_task(*args, **kwargs)

    def spawn_task(self, *args, **kwargs):
        if _my.ctx.current_launch:
            return _my.ctx.current_launch.spawn_task(self, *args, **kwargs)
        return TaskLaunch().spawn_task(self, *args, **kwargs)

    def execute_task(self, raw_args, user_data, proc):
        raw_arg_ptr = ffi.new('char[]', bytes(raw_args))
        raw_arg_size = len(raw_args)

        # Execute preamble to obtain Legion API context.
        task = ffi.new('legion_task_t *')
        raw_regions = ffi.new('legion_physical_region_t **')
        num_regions = ffi.new('unsigned *')
        context = ffi.new('legion_context_t *')
        runtime = ffi.new('legion_runtime_t *')
        c.legion_task_preamble(
            raw_arg_ptr, raw_arg_size, proc,
            task, raw_regions, num_regions, context, runtime)

        # Decode arguments from Pickle format.
        if c.legion_task_get_is_index_space(task[0]):
            arg_ptr = ffi.cast('char *', c.legion_task_get_local_args(task[0]))
            arg_size = c.legion_task_get_local_arglen(task[0])
        else:
            arg_ptr = ffi.cast('char *', c.legion_task_get_args(task[0]))
            arg_size = c.legion_task_get_arglen(task[0])

        if arg_size > 0 and c.legion_task_get_depth(task[0]) > 0:
            args = pickle.loads(ffi.unpack(arg_ptr, arg_size))
        else:
            args = ()

        # Unpack regions.
        regions = []
        for i in xrange(num_regions[0]):
            regions.append(raw_regions[0][i])

        # Unpack physical regions.
        if self.privileges is not None:
            req = 0
            for i, arg in zip(range(len(args)), args):
                if isinstance(arg, Region):
                    assert req < num_regions[0] and req < len(self.privileges)
                    instance = raw_regions[0][req]
                    req += 1

                    priv = self.privileges[i]
                    if hasattr(priv, 'fields'):
                        assert set(priv.fields) <= set(arg.fspace.field_ids.keys())
                    for name, fid in arg.fspace.field_ids.items():
                        if not hasattr(priv, 'fields') or name in priv.fields:
                            arg._set_instance(name, instance, priv)
            assert req == num_regions[0]

        # Build context.
        ctx = Context(context, runtime, task, regions)

        # Ensure that we're not getting tangled up in another
        # thread. There should be exactly one thread per task.
        try:
            _my.ctx
        except AttributeError:
            pass
        else:
            raise Exception('thread-local context already set')

        # Store context in thread-local storage.
        _my.ctx = ctx

        # Execute task body.
        result = self.body(*args)

        # Mark any remaining objects as escaped.
        for ref in ctx.owned_objects:
            obj = ref()
            if obj is not None:
                obj.escaped = True

        # Encode result.
        if not self.return_type:
            result_str = pickle.dumps(result, protocol=_pickle_version)
            result_size = len(result_str)
            result_ptr = ffi.new('char[]', result_size)
            ffi.buffer(result_ptr, result_size)[:] = result_str
        else:
            if self.return_type.size > 0:
                result_ptr = ffi.new(ffi.getctype(self.return_type.cffi_type, '*'), result)
            else:
                result_ptr = ffi.NULL
            result_size = self.return_type.size

        # Execute postamble.
        c.legion_task_postamble(runtime[0], context[0], result_ptr, result_size)

        # Clear thread-local storage.
        del _my.ctx

    def register(self, task_id, top_level_task):
        assert(self.task_id is None)

        if not task_id:
            if not top_level_task:
                global next_legion_task_id
                task_id = next_legion_task_id
                next_legion_task_id += 1
                # If we ever hit this then we need to allocate more task IDs
                assert task_id < max_legion_task_id
            else:
                task_id = 1 # Predefined value for the top-level task

        execution_constraints = c.legion_execution_constraint_set_create()
        c.legion_execution_constraint_set_add_processor_constraint(
            execution_constraints, c.PY_PROC)

        layout_constraints = c.legion_task_layout_constraint_set_create()
        # FIXME: Add layout constraints

        options = ffi.new('legion_task_config_options_t *')
        options[0].leaf = self.leaf
        options[0].inner = self.inner
        options[0].idempotent = self.idempotent
        options[0].replicable = self.replicable

        qualname = get_qualname(self.body)
        task_name = ('%s.%s' % (self.body.__module__, '.'.join(qualname)))

        c_qualname_comps = [ffi.new('char []', comp.encode('utf-8')) for comp in qualname]
        c_qualname = ffi.new('char *[]', c_qualname_comps)

        global global_task_registration_barrier
        if global_task_registration_barrier is not None:
            c.legion_phase_barrier_arrive(_my.ctx.runtime, _my.ctx.context, global_task_registration_barrier, 1)
            global_task_registration_barrier = c.legion_phase_barrier_advance(_my.ctx.runtime, _my.ctx.context, global_task_registration_barrier)
            c.legion_phase_barrier_wait(_my.ctx.runtime, _my.ctx.context, global_task_registration_barrier)

        c.legion_runtime_register_task_variant_python_source_qualname(
            c.legion_runtime_get_runtime(),
            task_id,
            task_name.encode('utf-8') if top_level_task else ffi.NULL,
            top_level_task, # Global
            execution_constraints,
            layout_constraints,
            options[0],
            self.body.__module__.encode('utf-8'),
            c_qualname,
            len(qualname),
            ffi.NULL,
            0)

        if global_task_registration_barrier is not None:
            c.legion_phase_barrier_arrive(_my.ctx.runtime, _my.ctx.context, global_task_registration_barrier, 1)
            global_task_registration_barrier = c.legion_phase_barrier_advance(_my.ctx.runtime, _my.ctx.context, global_task_registration_barrier)
            c.legion_phase_barrier_wait(_my.ctx.runtime, _my.ctx.context, global_task_registration_barrier)

        c.legion_execution_constraint_set_destroy(execution_constraints)
        c.legion_task_layout_constraint_set_destroy(layout_constraints)

        self.task_id = task_id
        return self

def task(body=None, **kwargs):
    if body is None:
        return lambda body: task(body, **kwargs)
    return Task(body, **kwargs)

class _TaskLauncher(object):
    __slots__ = ['task']

    def __init__(self, task):
        self.task = task

    def preprocess_args(self, args):
        return [
            arg._legion_preprocess_task_argument()
            if hasattr(arg, '_legion_preprocess_task_argument') else arg
            for arg in args]

    def gather_futures(self, args):
        normal = []
        futures = []
        for arg in args:
            if isinstance(arg, Future):
                arg = Future(arg, argument_number=len(futures))
                futures.append(arg)
            normal.append(arg)
        return normal, futures

    def encode_args(self, args):
        task_args = ffi.new('legion_task_argument_t *')
        task_args_buffer = None
        if self.task.calling_convention == 'python':
            arg_str = pickle.dumps(args, protocol=_pickle_version)
            task_args_buffer = ffi.new('char[]', arg_str)
            task_args[0].args = task_args_buffer
            task_args[0].arglen = len(arg_str)
        elif self.task.calling_convention == 'regent':
            arg_struct = self.task.argument_struct(args)
            task_args_buffer = ffi.new('%s*' % arg_struct)
            # FIXME: Correct for > 64 arguments.
            getattr(task_args_buffer, '__map')[0] = 0 # Currently we never pass futures.
            for i, arg in enumerate(args):
                arg_name = '__arg_%s' % i
                arg_value = arg
                if hasattr(arg, 'handle'):
                    arg_value = arg.handle[0]
                setattr(task_args_buffer, arg_name, arg_value)
            for i, arg in enumerate(args):
                if isinstance(arg, Region):
                    for j, field_id in enumerate(arg.fspace.field_ids.values()):
                        arg_name = '__arg_%s_field_%s' % (i, j)
                        setattr(task_args_buffer, arg_name, field_id)
            task_args[0].args = task_args_buffer
            task_args[0].arglen = ffi.sizeof(arg_struct)
        else:
            # FIXME: External tasks need a dedicated calling
            # convention to permit the passing of task arguments.
            task_args[0].args = ffi.NULL
            task_args[0].arglen = 0
        # WARNING: Need to return the interior buffer or else it will be GC'd
        return task_args, task_args_buffer

    def spawn_task(self, *args, **kwargs):
        # Hack: workaround for Python 2 not having keyword-only arguments
        def validate_spawn_task_args(point=None):
            return point
        point = validate_spawn_task_args(**kwargs)

        assert(isinstance(_my.ctx, Context))

        args = self.preprocess_args(args)
        args, futures = self.gather_futures(args)
        task_args, _ = self.encode_args(args)

        # Construct the task launcher.
        launcher = c.legion_task_launcher_create(
            self.task.task_id, task_args[0], c.legion_predicate_true(), 0, 0)
        if point is not None:
            if not isinstance(point, DomainPoint):
                point = DomainPoint.create(point)
            c.legion_task_launcher_set_point(launcher, point.raw_value())
        for i, arg in zip(range(len(args)), args):
            if isinstance(arg, Region):
                assert i < len(self.task.privileges)
                priv = self.task.privileges[i]
                req = c.legion_task_launcher_add_region_requirement_logical_region(
                    launcher, arg.handle[0],
                    priv._legion_privilege(),
                    0, # EXCLUSIVE
                    arg.parent.handle[0] if arg.parent is not None else arg.handle[0],
                    0, False)
                if hasattr(priv, 'fields'):
                    assert set(priv.fields) <= set(arg.fspace.field_ids.keys())
                for name, fid in arg.fspace.field_ids.items():
                    if not hasattr(priv, 'fields') or name in priv.fields:
                        c.legion_task_launcher_add_field(
                            launcher, req, fid, True)
            elif isinstance(arg, Future):
                c.legion_task_launcher_add_future(launcher, arg.handle)
            elif self.task.calling_convention is None:
                # FIXME: Task arguments aren't being encoded AT ALL;
                # at least throw an exception so that the user knows
                raise Exception('External tasks do not support non-region arguments')

        # Launch the task.
        result = c.legion_task_launcher_execute(
            _my.ctx.runtime, _my.ctx.context, launcher)
        c.legion_task_launcher_destroy(launcher)

        # Build future of result.
        future = Future.from_cdata(result, value_type=self.task.return_type)
        c.legion_future_destroy(result)
        return future

class _IndexLauncher(_TaskLauncher):
    __slots__ = ['task', 'domain', 'local_args', 'future_args', 'future_map']

    def __init__(self, task, domain):
        super(_IndexLauncher, self).__init__(task)
        self.domain = domain
        self.local_args = c.legion_argument_map_create()
        self.future_args = []
        self.future_map = None

    def __del__(self):
        c.legion_argument_map_destroy(self.local_args)

    def spawn_task(self, *args):
        raise Exception('IndexLaunch does not support spawn_task')

    def attach_local_args(self, index, *args):
        task_args, _ = self.encode_args(args)
        c.legion_argument_map_set_point(
            self.local_args, index.value.raw_value(), task_args[0], False)

    def attach_future_args(self, *args):
        self.future_args = args

    def launch(self):
        # All arguments are passed as local, so global is NULL.
        global_args = ffi.new('legion_task_argument_t *')
        global_args[0].args = ffi.NULL
        global_args[0].arglen = 0

        # Construct the task launcher.
        launcher = c.legion_index_launcher_create(
            self.task.task_id, self.domain.raw_value(),
            global_args[0], self.local_args,
            c.legion_predicate_true(), False, 0, 0)

        for arg in self.future_args:
            c.legion_index_launcher_add_future(launcher, arg.handle)

        # Launch the task.
        result = c.legion_index_launcher_execute(
            _my.ctx.runtime, _my.ctx.context, launcher)
        c.legion_index_launcher_destroy(launcher)

        # Build future (map) of result.
        self.future_map = FutureMap(result)
        c.legion_future_map_destroy(result)

class TaskLaunch(object):
    __slots__ = []
    def spawn_task(self, task, *args, **kwargs):
        launcher = _TaskLauncher(task=task)
        return launcher.spawn_task(*args, **kwargs)

class _IndexValue(object):
    __slots__ = ['value']
    def __init__(self, value):
        self.value = value
    def __int__(self):
        return self.value.__int__()
    def __index__(self):
        return self.value.__index__()
    def __str__(self):
        return str(self.value)
    def __repr__(self):
        return repr(self.value)
    def _legion_preprocess_task_argument(self):
        return self.value

class _FuturePoint(object):
    __slots__ = ['launcher', 'point', 'future']
    def __init__(self, launcher, point):
        self.launcher = launcher
        self.point = point
        self.future = None
    def get(self):
        if self.future is not None:
            return self.future.get()

        if self.launcher.future_map is None:
            raise Exception('Cannot retrieve a future from an index launch until the launch is complete')

        self.future = self.launcher.future_map[self.point]

        # Clear launcher and point
        del self.launcher
        del self.point

        return self.future.get()

class IndexLaunch(object):
    __slots__ = ['domain', 'launcher', 'point',
                 'saved_task', 'saved_args']

    def __init__(self, domain):
        if isinstance(domain, Domain):
            self.domain = domain
        elif isinstance(domain, Ispace):
            self.domain = ispace.domain
        else:
            self.domain = Domain.create(domain)
        self.launcher = None
        self.point = None
        self.saved_task = None
        self.saved_args = None

    def __iter__(self):
        _my.ctx.begin_launch(self)
        self.point = _IndexValue(None)
        for i in self.domain:
            self.point.value = i
            yield self.point
        _my.ctx.end_launch(self)
        self.launch()

    def ensure_launcher(self, task):
        if self.launcher is None:
            self.launcher = _IndexLauncher(task=task, domain=self.domain)

    def check_compatibility(self, task, *args):
        # The tasks in a launch must conform to the following constraints:
        #   * Only one task can be launched.
        #   * The arguments must be compatible:
        #       * At a given argument position, the value must always
        #         be a special value, or always not.
        #       * Special values include: regions and futures.
        #       * If a region, the value must be symbolic (i.e. able
        #         to be analyzed as a function of the index expression).
        #       * If a future, the values must be literally identical
        #         (i.e. each argument slot in the launch can only
        #         accept a single future value.)

        if self.saved_task is None:
            self.saved_task = task
        if task != self.saved_task:
            raise Exception('An IndexLaunch may contain only one task launch')

        if self.saved_args is None:
            self.saved_args = args
        for arg, saved_arg in zip_longest(args, self.saved_args):
            # TODO: Add support for region arguments
            if isinstance(arg, Region) or isinstance(arg, RegionField):
                raise Exception('TODO: Support region arguments to an IndexLaunch')
            elif isinstance(arg, Future):
                if arg != saved_arg:
                    raise Exception('Future argument to IndexLaunch does not match previous value at this position')

    def spawn_task(self, task, *args):
        self.ensure_launcher(task)
        self.check_compatibility(task, *args)
        args = self.launcher.preprocess_args(args)
        args, futures = self.launcher.gather_futures(args)
        self.launcher.attach_local_args(self.point, *args)
        self.launcher.attach_future_args(*futures)
        # TODO: attach region args
        return _FuturePoint(self.launcher, self.point.value)

    def launch(self):
        self.launcher.launch()

@task(leaf=True)
def _dummy_task():
    return 1

def execution_fence(block=False):
    c.legion_runtime_issue_execution_fence(_my.ctx.runtime, _my.ctx.context)
    if block:
        _dummy_task().get()

class Tunable(object):
    # FIXME: Deduplicate this with DefaultMapper::DefaultTunables
    NODE_COUNT = 0
    LOCAL_CPUS = 1
    LOCAL_GPUS = 2
    LOCAL_IOS = 3
    LOCAL_OMPS = 4
    LOCAL_PYS = 5
    GLOBAL_CPUS = 6
    GLOBAL_GPUS = 7
    GLOBAL_IOS = 8
    GLOBAL_OMPS = 9
    GLOBAL_PYS = 10

    @staticmethod
    def select(tunable_id):
        result = c.legion_runtime_select_tunable_value(
            _my.ctx.runtime, _my.ctx.context, tunable_id, 0, 0)
        future = Future.from_cdata(result, value_type=uint64)
        c.legion_future_destroy(result)
        return future

def execute_as_script():
    args = input_args(True)
    if len(args) < 1:
        return False, False # no idea what's going on here, just return
    if os.path.basename(args[0]) != 'legion_python':
        return False, False # not in legion_python
    if len(args) < 2 or args[1].startswith('-'):
        return True, False # argument is a flag
    # If it has an extension, we're going to guess that it was
    # intended to be a script.
    return True, len(os.path.splitext(args[1])[1]) > 1

is_legion_python, is_script = execute_as_script()
if is_script:
    # We can't use runpy for this since runpy is aggressive about
    # cleaning up after itself and removes the module before execution
    # has completed.
    def run_path(filename, run_name=None):
        import imp
        module = imp.new_module(run_name)
        setattr(module, '__name__', run_name)
        setattr(module, '__file__', filename)
        setattr(module, '__loader__', None)
        setattr(module, '__package__', run_name.rpartition('.')[0])
        assert run_name not in sys.modules
        sys.modules[run_name] = module

        sys.path.append(os.path.dirname(filename))

        with open(filename) as f:
            code = compile(f.read(), filename, 'exec')
            exec(code, module.__dict__)

    @task(top_level=True, replicable=True)
    def legion_main():
        # FIXME: Really this should be the number of control replicated shards at this level
        global global_task_registration_barrier
        num_procs = Tunable.select(Tunable.GLOBAL_PYS).get()
        global_task_registration_barrier = c.legion_phase_barrier_create(_my.ctx.runtime, _my.ctx.context, num_procs)

        args = input_args(True)
        assert len(args) >= 2
        sys.argv = list(args)
        run_path(args[1], run_name='__legion_main__')
elif is_legion_python:
    print('WARNING: Executing Python modules via legion_python has been deprecated.')
    print('It is now recommended to run the script directly by passing the path')
    print('to legion_python.')
    print()
