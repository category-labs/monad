import ctypes
import hashlib
import importlib.util
import io
import pathlib
import sys

from dataclasses import dataclass

@dataclass
class EventInfo:
  c_name: str                       # C identifier name
  payload_type: ctypes.Structure    # Payload of C structure
  description: str                  # Text description of event

def create_event(*args) -> EventInfo:
  return EventInfo(*args)

def load_events() -> list[EventInfo]:
  # We're going to load event metadata definitions from '.py' files in the
  # 'definitions' directory. We load them in a well-defined order, so that
  # more "fundamental" events (like the recorder internal events) appear
  # earlier in the list, and thus earlier in the enumeration type in the
  # generated code
  def_dir = pathlib.Path(__file__).parent / 'definitions'
  def_files = ('internal', 'execution')
  py_files = tuple(def_dir / f'{file}.py' for file in def_files)

  events = list()
  for py_file in py_files:
    spec = importlib.util.spec_from_file_location(f'{py_file.stem}', py_file)
    def_module = importlib.util.module_from_spec(spec)
    def_module.__path__ = str(py_file.parent)
    def_module.register_event = lambda *args: events.append(create_event(*args))
    spec.loader.exec_module(def_module)
  return events

def hash_events(events: list[EventInfo]) -> bytes:
  # This can be incremented to change the hash code even when no event
  # definitions have changed, as a signal to external users that they must
  # recompile. As the name suggests, it is used when ABI-sensitive objects
  # in the shared memory region change, but it can also be used for the
  # PF_LOCAL protocol versioning
  SHMEM_ABI = 1

  fingerprint = io.BytesIO()
  fingerprint.write(SHMEM_ABI.to_bytes(length=4, byteorder=sys.byteorder))
  for enum_code, event in enumerate(events):
    fingerprint.write(enum_code.to_bytes(length=2, byteorder=sys.byteorder))
    fingerprint.write(event.c_name.encode())
    if not event.payload_type:
      continue
    if not issubclass(event.payload_type, ctypes.Structure):
      fingerprint.write(ctypes.sizeof(event.payload_type).to_bytes(
          length=8, byteorder=sys.byteorder))
      continue
    for field_name, field_type in event.payload_type._fields_:
      field = getattr(event.payload_type, field_name)
      fingerprint.write(field_name.encode())
      fingerprint.write(field_type.__name__.encode())
      fingerprint.write(field.offset.to_bytes(length=8, byteorder=sys.byteorder))
      fingerprint.write(field.size.to_bytes(length=8, byteorder=sys.byteorder))
  m = hashlib.sha256()
  m.update(fingerprint.getvalue())
  return m.digest()
