# Tree decomposition validity checker

This software verifies that a given, purported tree decomposition is a correct tree decomposition of a given graph. It is part of the first Parameterized Algorithms and Computational Experiments Challenge ([PACE 2016](https://pacechallenge.wordpress.com/track-a-treewidth/)).

## Usage

Check that input.gr and input.td correctly encode a graph and one of its tree decompositions:
```
./td-validate input.gr input.td
```

Check that input.gr correctly encodes a graph:
```
./td-validate input.gr
```

## Build

Run `make` and, optionally, `make test`.

## Credits

- Cornelius Brand
- Holger Dell
- Lukas Larisch
- Felix Salfelder

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details
