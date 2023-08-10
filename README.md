# Dataflow

The objective of this project was to create a uC compiler using Python. The 
compiler is able to compile uC code to uCIR code, and then optimize it using 
dataflow analysis.

## Tasks

We completed the following tasks

- [x] Implementation of the lexer in `uc/uc_lexer.py`
- [x] Implementation of the parser in `uc/uc_parser.py`
- [x] Implementation of the ast in `uc/uc_ast.py`
- [x] Implementation of the semantic analysis in `uc/uc_sema.py`
- [x] Implementation of the type system in `uc/uc_type.py`
- [x] Implementation of the code generation in `uc/uc_code.py`
- [x] Implementation of basic blocks in `uc/uc_block.py`
- [x] Implementation of the dataflow analysis in `uc/uc_analysis.py`

## Requirements

Use Python 3.7 or a newer version.    
Required pip packages:
- ply, pytest, setuptools, graphviz, pathlib

### Docker
Alternatively you can also use Docker & Docker Compose (Docker Engine 19.03.0+) if you don't
want to setup a local environment.

## Running

After you have accepted this assignment on the course's Github Classroom page,
clone it to your machine.

You can run `uc_analysis.py` directly with python. For more information, run:
```sh
    python3 uc/uc_analysis.py -h
```
You can use the inputs available inside
the `tests/in-out/` directory.

The `uc_compiler.py` script is also available, it can be run through its
symbolic link at the root of the repo (`ucc`). For more information, run:
```sh
    ./ucc -h
```

### Docker
If you're using the dockerized environment, to run `uc_code.py` directly you should run:
```sh
docker-compose run --rm test uc/uc_code.py -h
``` 

```sh
# Example: running test 01
docker-compose run --rm test uc/uc_code.py tests/in-out/t01.in
``` 

## Testing with Pytest

You can run all the tests in `tests/in-out/` automatically with `pytest`. For
that, you first need to make the source files visible to the tests. There are
two options:
- Install your project in editable mode using the `setup.py` file from the root
  of the repo
```sh
    pip install -e .
```
- Or, add the repo folder to the PYTHONPATH environment variable with `setup.sh`
```sh
    source setup.sh
```

### Docker
Running all tests in the dockerized environment:
```sh
# When installing Docker on linux, this is a way you can use compose.
# For Mac and Windows, don't forget the hyphen on docker-compose.
docker compose run --rm pytest
``` 

Then you should be able to run all the tests by running `pytest` at the root
of the repo.

### Linting and Formatting

This step is **optional**. Required pip packages:
- flake8, black, isort

You can lint your code with two `flake8` commands from the root of the repo:
```sh
    flake8 . --count --select=E9,F63,F7,F82 --show-source --statistics
    flake8 . --count --exit-zero --max-line-length=120 --statistics
```

The first command shows errors that need to be fixed and will cause your
commit to fail. The second shows only warnings that are suggestions for
a good coding style.

To format the code, you can use `isort` to manage the imports and `black`
for the rest of the code. Run both from the root of the repo:
```sh
    isort .
    black .
```
