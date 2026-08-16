# Worked examples

The examples are organized by what they teach about the public API. They are not separate proof engines: each defines a `Core.ProblemDefinition`, registers strategy data, declares a Blueprint or Program, and reads the theorem from the sealed report.

## Minimal Core declaration

Start with the smallest complete example. It shows the exact boundary without domain adapters or unrelated infrastructure.

## Graph registration

The Graph example shows how finite graph objects and invariance enter the Problem and Target while Core strategy registrations remain domain-neutral.

## PDE registration

The PDE example shows a represented analytic object using the same problem, target, strategy-data, and DAG interfaces.

## Larger routed program

The Erdős example demonstrates multiple indexed families, nested dichotomies, metadata, shared forward continuation blocks, and report inspection in one application.
