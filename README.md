hott-reals
===

A formalization of the HoTT book construction of the Cauchy reals as a higher inductive type. Our goal is to formalize various topics in constructive analysis with this as a foundation.

References:

- The Univalent Foundations Program, [*Homotopy Type Theory: Univalent Foundations of Mathematics*](https://homotopytypetheory.org/book/) (2013), Section 11.3.
- Gaëtan Gilbert, [*Formalising Real Numbers in Homotopy Type Theory*](https://doi.org/10.1145/3018610.3018614) (CPP 2017).
- Auke Booij, [*Analysis in Univalent Type Theory*](https://etheses.bham.ac.uk/id/eprint/10411/) (PhD thesis, Birmingham, 2020).

Our previous work:

- Lorenzo Molena, Marcin Jan Turek-Grzybowski and Riccardo Borsetto, [*A Cubical Path from Algebra to Analysis*](https://types2026.cse.chalmers.se/abstracts/51.pdf) (TYPES 2026 abstract).
- Jackson Brough, [*Formalizing the Real Numbers in Homotopy Type Theory with Cubical Agda*](https://arxiv.org/abs/2604.24782) (undergraduate thesis, 2026).

Content
---

We are currently in the process of cleaning up previous versions of our work and adding them to the `glowny` branch ("main" in Polish). A version of the formalization that combined work from several members of our group can be found on the [`beans`](https://github.com/utahplt/hott-reals/tree/beans) branch, and the original content for Brough's thesis can be found at the [`thesis`](https://github.com/utahplt/hott-reals/tree/thesis) tag.

Right now, the content is just enough to get started:

| Library                 | Depends on         | Contents                                                |
|-------------------------|--------------------|---------------------------------------------------------|
| `hott-reals-order`      | utahplt/cubical    | ordered abelian groups, lattice and ordered ring lemmas |
| `hott-reals-completion` | utahplt/cubical    | the completion of a premetric space                     |
| `hott-reals`            | `hott-reals-order` | the main library                                        |

We need to go through the Agda on the `beans` branch and port it here, cleaning things up along the way. We also need to clean up the natural language blueprint and sync it up with the Agda content. Roughly, this will include:

Premetric completions

- [ ] Eliminators
- [ ] Properties of closeness, for example that the completion is a complete premetric space
- [ ] Extension principles for various classes of functions

Reals

- [ ] Definition
- [ ] Algebra: addition, lattice, multiplication, reciprocal
- [ ] Order: non-strict and strict inequality, addition compatibility, magnitude, multiplication compatibility
- [ ] Archimedean ordered field
- [ ] Universal property

Setup
---

We package Agda, our cubical fork, and the inter-dependencies of each library with Nix. You can install Nix by following [its installation guide](https://nixos.org/download/).

We have a Cachix cache for our fork of cubical. Add this to `/etc/nix/nix.conf` (or `nix.settings` on NixOS):

```
experimental-features = nix-command flakes
extra-substituters = https://hott-reals.cachix.org
extra-trusted-public-keys = hott-reals.cachix.org-1:rgyQbU9OCqP0UDpSktfNL4ogjZKb45Tq2ZhLpmfRP6I=
```

If you are missing the `extra-substituters` and `extra-trusted-public-keys` Nix will have to run Agda type checking for our cubical fork whenever it is updated, which is really slow and annoying.

To check everything is happy:

```
nix flake check
```

The provided dev shell includes Agda and writes a `.agda/libraries` file so that edits to one library are visible to the others inside the environment. You can enter the dev shell with `nix develop`. There is a `.envrc` file if you use direnv. When you add a library, make sure to re-enter the dev shell (or run `direnv reload`) to update the `.agda/libraries` file.

Editors:

- Emacs: use [envrc](https://github.com/purcell/envrc) or [direnv.el](https://github.com/wbolster/emacs-direnv) if you want to avoid having to launch Emacs from within the dev shell.
- VSCode: use the agda-mode (banacorn) and direnv (mkhl) extensions, and use `agda` from the dev shell instead of the Agda language server that the agda-mode extension might offer to download.

Development
---

Ultimately, our goal is to get much of this content merged into [agda/cubical](https://github.com/agda/cubical). However, it is too much for one PR, so the plan is to develop the content here and then make small, incremental PRs to cubical. There are two open now:

- https://github.com/agda/cubical/pull/1331: Heyting, ordered, and Archimedean fields
- https://github.com/agda/cubical/pull/1333: Positive rationals and premetric spaces

The libraries here depend on a fork of cubical, [`utahplt/cubical`](https://github.com/utahplt/cubical), with all our open pull requests merged.

There are several libraries (`hott-reals`, `hott-reals-order`, `hott-reals-completion`). The idea is that new work starts in `hott-reals`. When the boundaries of a topic become clear, code can be moved to a dedicated library, e.g. `hott-reals-completion`. Then, when it is ready, we can make small adjustments to turn a given library into a PR to cubical.

### Adding a new library

1. Create `libraries/<name>/<name>.agda-lib`:

   ```
   name: <name>
   include: .
   depend:
     cubical
     hott-reals-order
   flags: --cubical --no-import-sorts --guardedness --safe
   ```

2. Add it to the `libraries` attribute set in `flake.nix` with its dependencies:

   ```
   <name> = library "<name>" [ cubical' hott-reals-order ];
   ```

3. Add a row to the table in *Content* above.

### Upstreaming

When a library is ready to be converted to a PR to agda/cubical:

1. Copy the library modules into a branch of your cubical fork off master, rename `HoTTReals` to `Cubical`, and get it to type check.
2. Open a pull request.
3. Merge that branch into the `hott-reals` branch of the `utahplt/cubical` fork.
4. In this repository, bump the fork version with `nix flake update cubical`, delete the copied modules, change imports from `HoTTReals` to `Cubical` where necessary, and ensure everything type checks.

When a PR is open, changes should be made to the PR branch first, and then those changes can be merged into the fork again. When PRs are merged, we just need to merge `upstream/master` into the `utahplt/cubical` fork.

### Updating the cubical fork

In a checkout of utahplt/cubical with remotes `upstream` (agda/cubical) and `origin` (utahplt/cubical):

```
git switch hott-reals
git pull --ff-only origin hott-reals
git fetch upstream master
git merge upstream/master
git push origin hott-reals
```

To add a new open pull request to the fork, or to merge new commits from an open one:

```
git fetch upstream +pull/<n>/head:pr/<n>
git merge pr/<n>
```

Then in this repository:

```
nix flake update cubical
```
