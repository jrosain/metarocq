{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "metarocq";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "rocq-9.0";

  # MetaRocq is expected to be compatible with a single coq version
  # The name of the bundle should finish with the coq version to use
  # cachedMake.sh
  bundles."rocq-9.0" = {
    rocqPackages.rocq-core.override.version = "9.0";
    rocqPackages.equations.override.version = "1.3.1-9.0";

    # rocqPackages.metarocq-utils.main-job = true; # Probably won't work until this work is upstreamed to nixpkgs

    push-branches = ["9.0"];

    # Reverse dependencies
    # rocqPackages.ElmExtraction.override.version = "rocq-9.0"; # Doesn't support 9.0 yet
    # rocqPackages.RustExtraction.override.version = "rocq-9.0"; # Doesn't support 9.0 yet
  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.coq-community = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  cachix.metacoq.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
