# ACTRIS COQ DEVELOPMENT

This directory contains the artifact for the paper "Actris: Session Type
Based Reasoning in Separation Logic".

It has been built and tested with the following dependencies

 - Coq 8.9.1
 - [std++](https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp) at
   commit f9830af6.
 - [iris](https://gitlab.mpi-sws.org/iris/iris) at
   commit 0c4e2984.

In order to build, install the above dependencies and then run
`make -j [num CPU cores]` to compile Actris.

## Directory structure

### Theory

The theory can be found in `theories/channel`. Some used utilities can be found
in `theories/utils`.

The files correspond to the following:

- `theories/channel/channel.v`: The definitional semantics of bidirectional
  channels in HeapLang.
- `theories/channel/proto_model.v`: The CPS model of dependent separation
  protocols.
- `theories/channel/proto_channel.v`: The definition of the connective `↣` for
  channel ownership and the proof rules of the Actris logic.
- `theories/channel/proofmode.v`: The Coq tactics for symbolic execution.

### Examples

The examples can be found in `theories/examples`.

The following list gives a mapping between the examples in the paper and their
mechanization in Coq:

* 1. Introduction: `theories/examples/basics.v`
* 2. Tour of Actris
  * 2.3 Basic, sort: `theories/examples/sort.v`
  * 2.4 Higher-Order Functions, sort_func: `theories/examples/sort.v`
  * 2.5 Branching: `theories/examples/sort_br_del.v`
  * 2.6 Recursion: `theories/examples/sort_br_del.v`
  * 2.7 Delegation: `theories/examples/sort_br_del.v`
  * 2.8 Dependent: `theories/examples/sort_fg.v`
* 3. Manifest sharing via locks
  * 3.1 Sample program: `theories/examples/basics.v`
  * 3.2 Distributed mapper: `theories/examples/map.v`
* 4. Case study: map reduce:
  * Utilities for shuffling/grouping: `theories/utils/group.v`
  * Implementation and verification: `theories/examples/map_reduce.v`

## Differences between the formalization and the paper

There are a number of small differences between the paper presentation
of Actris and the formalization in Coq, that are briefly discussed here.

### Connectives for physical ownership of channels

In the paper physical ownership of a channel is formalized using a single
connective `(c1,c2) ↣ (vs1,vs2)`, while the mechanisation has two connectives
for the endpoints and one for connecting them, namely:

- `chan_own γ Left vs1` and `chan_own γ Right vs1`
- `is_chan N γ c1 c2`

Where `γ` is a ghost name and `N` the invariant used internally. This setup is
less intuitive but gives rise to a more practical Jacobs/Piessens-style spec
of `recv` that does not need a closing view shift (to handle the case that
the buffer is empty).

### Later modalities in primitive rules for channels

The primitive rules for `send` and `recv` (`send_spec` and `recv_spec`) contain
three later modalities, which are omitted for brevity's sake in the paper. These
later modalities expose that these operations perform at least three steps in
the operational semantics, and are needed to deal with the three levels of
indirection in the invariant for protocols: 1.) the `▶` in the CPS encoding of
protocols, 2.) the higher-order ghost state used for ownership of protocols,
3.) the opening of the protocol invariant.
