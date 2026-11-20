"""References for the decoders driver: the protobuf wire format and the gossipsub RPC."""

# pb_records <hex>   The records by a reader written from the encoding guide, by the protobuf
#                    package (its unknown fields of a message of no fields), and what was seen.
# rpc <hex>          The RPC by a model of the libp2p schema with EthLib's documented choices, by
#                    the protobuf package with that schema, its bytes written again, what was seen.
#
# The schema is that of the libp2p specifications, written here as the table SCHEMA:
#
#   pubsub/README.md              RPC, RPC.SubOpts, Message
#   gossipsub-v1.0.md             ControlMessage, ControlIHave, ControlIWant, ControlGraft
#   gossipsub-v1.1.md             ControlPrune, PeerInfo
#   gossipsub-v1.2.md             ControlIDontWant
#   extensions/extensions.proto   ControlExtensions, PartialMessagesExtension, the new fields
#
# The experimental fields of extensions.proto (6492434 and 6492435) are left out, so both
# references see them as fields that the schema does not name.

from decoders_util import tohex, unhex
from google.protobuf import descriptor_pb2, descriptor_pool, message_factory, unknown_fields

# Field number: label, type, message type.
SCHEMA = {
    "RPC": {
        1: ("subscriptions", "repeated", "message", "SubOpts"),
        2: ("publish", "repeated", "message", "Message"),
        3: ("control", "optional", "message", "ControlMessage"),
        10: ("partial", "optional", "message", "PartialMessagesExtension"),
    },
    "SubOpts": {
        1: ("subscribe", "optional", "bool", None),
        2: ("topicid", "optional", "string", None),
        3: ("requestsPartial", "optional", "bool", None),
        4: ("supportsSendingPartial", "optional", "bool", None),
    },
    "Message": {
        1: ("from", "optional", "string", None),
        2: ("data", "optional", "bytes", None),
        3: ("seqno", "optional", "bytes", None),
        4: ("topic", "required", "string", None),
        5: ("signature", "optional", "bytes", None),
        6: ("key", "optional", "bytes", None),
    },
    "ControlMessage": {
        1: ("ihave", "repeated", "message", "ControlIHave"),
        2: ("iwant", "repeated", "message", "ControlIWant"),
        3: ("graft", "repeated", "message", "ControlGraft"),
        4: ("prune", "repeated", "message", "ControlPrune"),
        5: ("idontwant", "repeated", "message", "ControlIDontWant"),
        6: ("extensions", "optional", "message", "ControlExtensions"),
    },
    "ControlIHave": {
        1: ("topicID", "optional", "string", None),
        2: ("messageIDs", "repeated", "bytes", None),
    },
    "ControlIWant": {1: ("messageIDs", "repeated", "bytes", None)},
    "ControlGraft": {1: ("topicID", "optional", "string", None)},
    "ControlPrune": {
        1: ("topicID", "optional", "string", None),
        2: ("peers", "repeated", "message", "PeerInfo"),
        3: ("backoff", "optional", "uint64", None),
    },
    "PeerInfo": {
        1: ("peerID", "optional", "bytes", None),
        2: ("signedPeerRecord", "optional", "bytes", None),
    },
    "ControlIDontWant": {1: ("messageIDs", "repeated", "bytes", None)},
    "ControlExtensions": {10: ("partialMessages", "optional", "bool", None)},
    "PartialMessagesExtension": {
        1: ("topicID", "optional", "bytes", None),
        2: ("groupID", "optional", "bytes", None),
        3: ("partialMessage", "optional", "bytes", None),
        4: ("partsMetadata", "optional", "bytes", None),
    },
    "Empty": {},
}

FIELD = descriptor_pb2.FieldDescriptorProto
TYPES = {
    "bool": FIELD.TYPE_BOOL,
    "uint64": FIELD.TYPE_UINT64,
    "string": FIELD.TYPE_STRING,
    "bytes": FIELD.TYPE_BYTES,
    "message": FIELD.TYPE_MESSAGE,
}
LABELS = {
    "optional": FIELD.LABEL_OPTIONAL,
    "required": FIELD.LABEL_REQUIRED,
    "repeated": FIELD.LABEL_REPEATED,
}
# The wire type of each type of the schema.
WIRE = {"bool": 0, "uint64": 0, "string": 2, "bytes": 2, "message": 2}
# The fields that StrictNoSign forbids in a message.
SIGNED = (1, 3, 5, 6)


def build_classes():
    """The message classes of the schema, built from descriptors at run time."""
    file = descriptor_pb2.FileDescriptorProto(name="rpc.proto", package="pubsub", syntax="proto2")
    for name, fields in SCHEMA.items():
        message = file.message_type.add(name=name)
        for number, (field, label, kind, target) in fields.items():
            entry = message.field.add(
                name=field, number=number, type=TYPES[kind], label=LABELS[label]
            )
            if target:
                entry.type_name = ".pubsub." + target
    pool = descriptor_pool.DescriptorPool()
    pool.Add(file)
    find = pool.FindMessageTypeByName
    return {name: message_factory.GetMessageClass(find("pubsub." + name)) for name in SCHEMA}


CLASSES = build_classes()


class RefusedError(Exception):
    """The input is not what the reader accepts; the first word says which rule."""


# The wire format, from the encoding guide.


def read_varint(data, pos, seen):
    """A varint of at most ten bytes and a value below 2^64, as the guide bounds it."""
    value = 0
    for i in range(10):
        if pos + i >= len(data):
            raise RefusedError("varint")
        byte = data[pos + i]
        value |= (byte & 0x7F) << (7 * i)
        if byte < 0x80:
            if i > 0 and byte == 0:
                seen.add("padded-varint")
            if value >= 1 << 64:
                seen.add("varint-past-64-bits")
                raise RefusedError("varint")
            return value, pos + i + 1
    seen.add("varint-of-11-bytes")
    raise RefusedError("varint")


def read_key(data, pos, seen):
    key, after = read_varint(data, pos, seen)
    if after - pos > 5:
        seen.add("key-over-5-bytes")
    field = key >> 3
    if field == 0:
        seen.add("field-0")
        raise RefusedError("field-number")
    if field > (1 << 29) - 1:
        seen.add("field-past-2^29-1")
        raise RefusedError("field-number")
    return field, key & 7, after


def read_fixed(data, pos, count):
    if pos + count > len(data):
        raise RefusedError("truncated")
    return data[pos : pos + count], pos + count


def read_record(data, pos, seen, depth=0):
    """One record: its field, its wire type, its value, and the position after it."""
    field, wire, pos = read_key(data, pos, seen)
    if wire == 0:
        value, pos = read_varint(data, pos, seen)
    elif wire == 1:
        value, pos = read_fixed(data, pos, 8)
    elif wire == 2:
        size, after = read_varint(data, pos, seen)
        if after - pos > 5:
            seen.add("length-over-5-bytes")
        pos = after
        try:
            value, pos = read_fixed(data, pos, size)
        except RefusedError:
            seen.add("length-past-the-input")
            raise
    elif wire == 3:
        seen.add("nested-group" if depth else "group")
        value = []
        while True:
            if pos >= len(data):
                seen.add("group-not-closed")
                raise RefusedError("varint")
            # The end of a group is a key of wire type 4 with the number of its start.
            inner, inner_wire, after = read_key(data, pos, seen)
            if inner_wire == 4:
                if inner != field:
                    seen.add("group-end-of-another-field")
                    raise RefusedError("group-end")
                pos = after
                break
            record, pos = read_record(data, pos, seen, depth + 1)
            value.append(record)
    elif wire == 5:
        value, pos = read_fixed(data, pos, 4)
    else:
        seen.add("group-end-alone" if wire == 4 else "wire-type-6-or-7")
        raise RefusedError("wire-type")
    return (field, wire, value), pos


def read_records(data, seen):
    records, pos = [], 0
    while pos < len(data):
        record, pos = read_record(data, pos, seen)
        records.append(record)
    return records


def show_record(record):
    """A record as EthLib holds it: a group keeps no content."""
    field, wire, value = record
    if wire == 0:
        return f"{field}:0:{value}"
    if wire == 3:
        return f"{field}:3:"
    return f"{field}:{wire}:{value.hex()}"


def show_unknown(fields):
    """The unknown fields of a parsed message, in the same text."""
    out = []
    for field in fields:
        if field.wire_type == 0:
            out.append(f"{field.field_number}:0:{field.data}")
        elif field.wire_type == 3:
            out.append(f"{field.field_number}:3:")
        elif field.wire_type == 1:
            out.append(f"{field.field_number}:1:{field.data.to_bytes(8, 'little').hex()}")
        elif field.wire_type == 5:
            out.append(f"{field.field_number}:5:{field.data.to_bytes(4, 'little').hex()}")
        else:
            out.append(f"{field.field_number}:2:{bytes(field.data).hex()}")
    return ",".join(out) or "-"


def features(seen):
    return ",".join(sorted(seen)) or "-"


def pb_records(data):
    data, seen = unhex(data), set()
    try:
        model = ",".join(show_record(r) for r in read_records(data, seen)) or "-"
    except RefusedError as e:
        model = "error:" + str(e)
    try:
        message = CLASSES["Empty"]()
        message.ParseFromString(data)
        package = show_unknown(unknown_fields.UnknownFieldSet(message))
    except Exception:
        package = "error"
    return f"{model} {package} {features(seen)}"


# The RPC, by the documented choices of EthLib over the schema.


def model_message(name, data, seen):
    """The fields of a message as a dictionary from field number to value."""
    records = read_records(data, seen)
    fields = SCHEMA[name]
    if name == "Message":
        for field, _, _ in records:
            if field in SIGNED:
                seen.add("signed-field")
                raise RefusedError("signed")
    out = {}
    for field, wire, value in records:
        if field not in fields:
            seen.add("unknown-field-of-wire-type-" + str(wire))
            continue
        _, label, kind, target = fields[field]
        if wire != WIRE[kind]:
            seen.add("named-field-with-another-wire-type")
            raise RefusedError("wire-type")
        if kind == "string":
            try:
                value.decode("utf-8")
            except UnicodeDecodeError:
                seen.add("string-not-utf8")
                raise RefusedError("utf8") from None
        if kind == "bool":
            if value > 1:
                seen.add("bool-above-1")
            value = value != 0
        if kind == "message":
            value = model_message(target, value, seen)
        if label == "repeated":
            out.setdefault(field, []).append(value)
        elif name == "RPC" and field == 3:
            # The control field: each occurrence is read alone, then their lists are joined.
            if field in out:
                seen.add("control-twice")
                merged = out[field]
                for number, entry in value.items():
                    if number == 6:
                        seen.add("extensions-twice" if 6 in merged else "extensions-in-later")
                        merged[6] = entry
                    else:
                        merged.setdefault(number, []).extend(entry)
            else:
                out[field] = value
        else:
            if field in out:
                if kind == "message":
                    seen.add("extensions-twice" if name == "ControlMessage" else "partial-twice")
                else:
                    seen.add("singular-field-twice")
            # The last one wins, and a message is kept whole.
            out[field] = value
    for field, (_, label, _, _) in fields.items():
        if label == "required" and field not in out:
            seen.add("message-without-topic")
            raise RefusedError("missing-topic")
    return out


def x(data):
    return "x" + bytes(data).hex()


def bit(flag):
    return "1" if flag else "0"


def ids(values):
    return "[" + ",".join(x(v) for v in values) + "]"


def show_model(rpc):
    """The canonical text of an RPC of the model."""

    def sub(s):
        return f"({bit(s.get(1))},{x(s.get(2, b''))},{bit(s.get(3))},{bit(s.get(4))})"

    def prune(p):
        peers = ",".join(f"({x(q.get(1, b''))},{x(q.get(2, b''))})" for q in p.get(2, []))
        return f"({x(p.get(1, b''))},[{peers}],{p.get(3, 0)})"

    control = rpc.get(3, {})
    lists = [
        ",".join(f"({x(h.get(1, b''))},{ids(h.get(2, []))})" for h in control.get(1, [])),
        ",".join(ids(w.get(1, [])) for w in control.get(2, [])),
        ",".join(x(g.get(1, b"")) for g in control.get(3, [])),
        ",".join(prune(p) for p in control.get(4, [])),
        ",".join(ids(d.get(1, [])) for d in control.get(5, [])),
    ]
    extensions = bit(control[6].get(10)) if 6 in control else "-"
    partial = "-"
    if 10 in rpc:
        p = rpc[10]
        options = ",".join(x(p[n]) if n in p else "~" for n in (3, 4))
        partial = f"({x(p.get(1, b''))},{x(p.get(2, b''))},{options})"
    subs = ",".join(sub(s) for s in rpc.get(1, []))
    messages = ",".join(f"({x(m.get(2, b''))},{x(m[4])})" for m in rpc.get(2, []))
    return (
        f"[{subs}][{messages}]{{" + "".join(f"[{part}]" for part in lists) + extensions + "}"
    ) + partial


def raw(text):
    """The bytes of a string field, which the package gives as bytes when not UTF-8."""
    return text if isinstance(text, bytes) else text.encode("utf-8")


def show_package(rpc):
    """The canonical text of an RPC of the protobuf package."""

    def sub(s):
        flags = f"{bit(s.requestsPartial)},{bit(s.supportsSendingPartial)}"
        return f"({bit(s.subscribe)},{x(raw(s.topicid))},{flags})"

    def prune(p):
        peers = ",".join(f"({x(q.peerID)},{x(q.signedPeerRecord)})" for q in p.peers)
        return f"({x(raw(p.topicID))},[{peers}],{p.backoff})"

    control = rpc.control
    lists = [
        ",".join(f"({x(raw(h.topicID))},{ids(h.messageIDs)})" for h in control.ihave),
        ",".join(ids(w.messageIDs) for w in control.iwant),
        ",".join(x(raw(g.topicID)) for g in control.graft),
        ",".join(prune(p) for p in control.prune),
        ",".join(ids(d.messageIDs) for d in control.idontwant),
    ]
    extensions = "-"
    if control.HasField("extensions"):
        extensions = bit(control.extensions.partialMessages)
    partial = "-"
    if rpc.HasField("partial"):
        p = rpc.partial
        options = ",".join(
            x(getattr(p, name)) if p.HasField(name) else "~"
            for name in ("partialMessage", "partsMetadata")
        )
        partial = f"({x(p.topicID)},{x(p.groupID)},{options})"
    subs = ",".join(sub(s) for s in rpc.subscriptions)
    messages = ",".join(f"({x(m.data)},{x(raw(m.topic))})" for m in rpc.publish)
    return (
        f"[{subs}][{messages}]{{" + "".join(f"[{part}]" for part in lists) + extensions + "}"
    ) + partial


def rpc(data):
    data, seen = unhex(data), set()
    try:
        model = show_model(model_message("RPC", data, seen))
    except RefusedError as e:
        model = "error:" + str(e)
    try:
        message = CLASSES["RPC"]()
        message.ParseFromString(data)
        # A message without a required field is not initialized, which a parser reports.
        package = show_package(message) if message.IsInitialized() else "error:required"
        again = tohex(message.SerializeToString()) if message.IsInitialized() else "-"
    except Exception:
        package, again = "error", "-"
    return f"{model} {package} {again} {features(seen)}"


HANDLERS = {"pb_records": pb_records, "rpc": rpc}
