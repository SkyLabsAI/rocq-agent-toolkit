Rocq Environment Data Plugin
============================

This Rocq plugin provides a new `Print JSON Environment` vernacular command
that displays information about the environment. Without arguments, the query
collects the whole contents of the environment. If arguments are given, the
query is restricted to constants and inductives whose module path starts with
either of the module paths given as argument.
