



import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
_aliases = {}
_absolute = re.compile(r'(?<![\w/<>])/(?:[^\s/\\"\x27<>(),;:=][^\s"\x27<>(),;]*)')
_windows = re.compile(r'(?<!\w)[A-Za-z]:[\\/][^\s"\x27<>(),;]+')

def root_path(value, name='path'):
    path = Path(value)
    if path.is_absolute() or re.match(r'^[A-Za-z]:[\\/]', str(value)) or '..' in path.parts:
        raise ValueError(name + ' must be relative to the extracted root')
    result = (ROOT / path).resolve()
    if not result.is_relative_to(ROOT):
        raise ValueError(name + ' must stay inside the extracted root')
    return result

def relative(path):
    return Path(path).resolve().relative_to(ROOT).as_posix()

def tool(variable, default):
    value = os.environ.get(variable, default)
    candidate = str(root_path(value, variable)) if '/' in value or '\\' in value else value
    found = shutil.which(candidate)
    if found is None:
        raise RuntimeError('Set ' + variable + ' to a relative executable path or a command on PATH')
    for p in {found, str(Path(found).resolve())}:
        _aliases[p] = Path(found).name
    return found

def clean(data):
    is_bytes = isinstance(data, bytes)
    if is_bytes and b'/' not in data and b'\\' not in data:
        return data
    value = data.decode('utf-8') if is_bytes else str(data)
    roots = {str(ROOT), str(ROOT).removeprefix('/private')}
    for root in sorted(roots, key=len, reverse=True):
        value = value.replace(root + '/', '').replace(root, '.')
    for path, label in sorted(_aliases.items(), key=lambda item: len(item[0]), reverse=True):
        value = value.replace(path, label)
     
    uris = []
    def keep_uri(match):
        uris.append(match.group(0))
        return '\x00URI' + str(len(uris) - 1) + '\x00'
    value = re.sub(r'\b(?:https?|urn):[^\s"\x27<>]+', keep_uri, value)
    value = re.sub(r'(["\x27])/(?!/)[^"\x27\n<>]*\1',
                   lambda m: m.group(1) + '<host-path omitted>' + m.group(1), value)
    value = _windows.sub('<host-path omitted>', value)
    value = _absolute.sub('<host-path omitted>', value)
    for i, uri in enumerate(uris):
        value = value.replace('\x00URI' + str(i) + '\x00', uri)
    return value.encode('utf-8') if is_bytes else value

def run(command, *, stdout=None, stderr=None, capture_output=False, text=False, **kwargs):
     
    try:
        result = subprocess.run(command, capture_output=True, **kwargs)
    except subprocess.TimeoutExpired as exc:
        if stdout is not None:
            stdout.write(clean(exc.stdout or b''))
        if stderr is not None:
            stderr.write(clean(exc.stderr or b''))
        raise RuntimeError('Native tool exceeded its time limit') from None
    out, err = clean(result.stdout), clean(result.stderr)
    if stdout is not None:
        stdout.write(out)
    if stderr is not None:
        stderr.write(err)
    if capture_output:
        return subprocess.CompletedProcess([], result.returncode,
            out.decode('utf-8') if text else out, err.decode('utf-8') if text else err)
    return subprocess.CompletedProcess([], result.returncode)

def check_output(command, *, text=False, **kwargs):
    result = run(command, capture_output=True, text=text, **kwargs)
    if result.returncode:
        raise RuntimeError('Native command failed: ' + str(clean(result.stderr)))
    return result.stdout

def entrypoint(main):
    try:
        main()
    except Exception as exc:
        print(clean(type(exc).__name__ + ': ' + str(exc)), file=sys.stderr)
        raise SystemExit(1) from None
