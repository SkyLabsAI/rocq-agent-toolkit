import importlib.util
import os
import sys
from pathlib import Path
from typing import Any


def load_module(module_path: Path, package_name: str | None = None) -> Any:
    """
    Loads a Python module from a given file path and executes its 'run' method.
    This version correctly configures the module to support relative imports
    (e.g., 'from . import dependency').
    """
    # 1. Check if the file exists
    if not os.path.exists(module_path):
        print(f"ERROR: Module file not found at path: {module_path}")
        sys.exit(1)

    # 2. Define package details for relative imports
    # A temporary name for the package structure
    DYNAMIC_PACKAGE_NAME = (
        "dynamically_loaded_pkg" if package_name is None else package_name
    )
    base_module_name = os.path.splitext(os.path.basename(module_path))[0]

    # The module must have a fully qualified name (e.g., pkg.module_name)
    module_name = f"{DYNAMIC_PACKAGE_NAME}.{base_module_name}"
    module_dir = os.path.dirname(os.path.abspath(module_path))

    # print(f"Attempting to load module '{module_name}' as part of package '{DYNAMIC_PACKAGE_NAME}' from: {module_path}")

    try:
        # 3. CRITICAL: Create the parent package entry in sys.modules first.
        # This defines the context needed for relative imports to resolve.
        if DYNAMIC_PACKAGE_NAME not in sys.modules:
            # Create a dummy package module specification
            package_spec = importlib.util.spec_from_loader(
                DYNAMIC_PACKAGE_NAME, None, is_package=True
            )
            if package_spec is None:
                raise ImportError("Failed to load package specification")
            package_module = importlib.util.module_from_spec(package_spec)

            # Define the path where sub-modules (like dependency.py) can be found
            package_module.__path__ = [module_dir]

            # Add the package module to the system cache
            sys.modules[DYNAMIC_PACKAGE_NAME] = package_module

        # 4. Create module specification from file location using the fully qualified name
        spec = importlib.util.spec_from_file_location(module_name, module_path)
        if spec is None:
            print(f"ERROR: Could not create module specification for {module_path}")
            if DYNAMIC_PACKAGE_NAME in sys.modules:
                del sys.modules[DYNAMIC_PACKAGE_NAME]
            raise ImportError(f"Failed ot load library {module_name} @ {module_path}")

        # 5. Create a new module object
        module = importlib.util.module_from_spec(spec)

        # 6. Add the fully qualified module to sys.modules
        sys.modules[module_name] = module

        # 7. CRITICAL: Set the __package__ attribute on the module object
        # This tells Python which package the module belongs to, allowing it to use `from . import ...`
        module.__package__ = DYNAMIC_PACKAGE_NAME

        # 8. Execute the module's code
        # This is where the code inside target_module.py is run, including its relative imports.
        if spec.loader:
            spec.loader.exec_module(module)
        else:
            raise ImportError("[spec.loader] is None")

        return module

    except Exception as e:
        print(f"An error occurred during module loading or execution: {e}")
        raise e
        # Optional: Clean up the module and package entries on failure
        # if DYNAMIC_PACKAGE_NAME in sys.modules:
        #     del sys.modules[DYNAMIC_PACKAGE_NAME]
        # if module_name in sys.modules:
        #     del sys.modules[module_name]


def load_definition(
    mod_path: Path, def_name: str, package_name: str | None = None
) -> Any:
    """
    Load a definition from a file.
    """
    result = load_module(mod_path)
    val = []
    for comp in def_name.split("."):
        if hasattr(result, comp):
            result = getattr(result, comp)
            val.append(comp)
        else:
            raise ImportError(f"Failed to extract {comp} from {'.'.join(val)}")
    return result


def load_from_str(desc: str, package_name: str | None = None) -> Any:
    """
    Load a value from a file. Uses the syntax `path/to/module.py:definition.to.load`.
    """
    mod_and_def = desc.rsplit(":", 1)
    if len(mod_and_def) == 2:
        return load_definition(Path(mod_and_def[0]), mod_and_def[1], package_name)
    else:
        return load_module(Path(mod_and_def[0]), package_name)
