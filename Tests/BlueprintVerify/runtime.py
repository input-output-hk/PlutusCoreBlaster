"""One native-loading policy for capture, verification and regression drivers."""
import os
from pathlib import Path

def lean_command():
    native = os.environ.get('ASSURANCE_NATIVE_LIBRARY')
    if not native:
        for directory in os.environ.get('LEAN_PATH', '').split(os.pathsep):
            for filename in ['libBlaster.dylib', 'libBlaster.so', 'Blaster.dll']:
                candidate = Path(directory).resolve().parent / filename
                if candidate.is_file():
                    native = str(candidate)
                    break
            if native:
                break
    command = [os.environ.get('LEAN', 'lean')]
    if native:
        native = str(Path(native).resolve(strict=True))
        os.environ['ASSURANCE_NATIVE_LIBRARY'] = native
        command.append('--load-dynlib=' + native)
    return command
