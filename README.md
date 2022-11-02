# klac
KL Agda course

## how to get it
```sh
git clone --recursive https://github.com/cmcmA20/klac
```

## if you already cloned it
```sh
git submodule update --init --recursive
```

## First step
Open any .agda file with your editor and try to typecheck it


## Setup your environment

### Using Guix

1. Install guix using your preferred method:

  - Guix System: available out of the box;
  - Arch Linux: [see arch wiki](https://wiki.archlinux.org/title/Guix);
  - Debian GNU/Linux: [guix is available since bullseye](https://packages.debian.org/bullseye/guix);
  - Ubuntu: [guix is available since impish](https://packages.ubuntu.com/impish/guix)
  - Other distros: [Use official binary distribution](http://guix.trop.in/en/manual/devel/en/html_node/Binary-Installation.html)

2. Issue this command to launch emacs in environment:

    ```
    guix time-machine -C channels.scm -- shell --pure --manifest=manifest.scm -- emacs -q -l init.el
    ```


### Using GHCup

1. Install [GHCup](https://www.haskell.org/ghcup/) using official documentation.

2. Install GHC and cabal:

   ```
   ghcup upgrade
   ghcup install ghc 9.2.4
   ghcup set ghc 9.2.4
   ghcup install cabal 3.6.2.0
   ghcup set cabal 3.6.2.0
   cabal update
   ```

3. Install Agda, it may take a while:

   ```
   cabal install Agda-2.6.2.2
   ```

4. Use emacs as your editor (commands for debian/ubuntu):

   ```
   sudo apt update
   sudo apt install emacs -y
   agda-mode setup
   agda-mode compile
   ```


### Other methods

Contributions are welcome
