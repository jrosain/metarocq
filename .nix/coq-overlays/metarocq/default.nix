{ lib, fetchzip,
  mkCoqDerivation, recurseIntoAttrs,  single ? false,
  coqPackages, coq, equations, version ? null }@args:
with builtins // lib;
let
  repo  = "metarocq";
  owner = "MetaRocq";
  defaultVersion = with versions; switch coq.coq-version [
      { case = "8.11"; out = "1.0-beta2-8.11"; }
      { case = "8.12"; out = "1.0-beta2-8.12"; }
      # Do not provide 8.13 because it does not compile with equations 1.3 provided by default (only 1.2.3)
      # { case = "8.13"; out = "1.0-beta2-8.13"; }
      { case = "8.14"; out = "1.0-8.14"; }
      { case = "8.15"; out = "1.0-8.15"; }
      { case = "8.16"; out = "1.0-8.16"; }
      { case = "dev"; out = "dev"; }
    ] null;
  release = {
    "1.0-beta2-8.11".sha256 = "sha256-I9YNk5Di6Udvq5/xpLSNflfjRyRH8fMnRzbo3uhpXNs=";
    "1.0-beta2-8.12".sha256 = "sha256-I8gpmU9rUQJh0qfp5KOgDNscVvCybm5zX4TINxO1TVA=";
    "1.0-beta2-8.13".sha256 = "sha256-IC56/lEDaAylUbMCfG/3cqOBZniEQk8jmI053DBO5l8=";
    "1.0-8.14".sha256 = "sha256-iRnaNeHt22JqxMNxOGPPycrO9EoCVjusR2s0GfON1y0=";
    "1.0-8.15".sha256 = "sha256-8RUC5dHNfLJtJh+IZG4nPTAVC8ZKVh2BHedkzjwLf/k=";
    "1.0-8.16".sha256 = "sha256-7rkCAN4PNnMgsgUiiLe2TnAliknN75s2SfjzyKCib/o=";
  };
  releaseRev = v: "v${v}";

  # list of core metarocq packages sorted by dependency order
  packages = [ "utils" "common" "template-rocq" "pcuic" "safechecker" "template-pcuic" "erasure" "quotation" "safechecker-plugin" "erasure-plugin" "all" ];

  template-rocq = metarocq_ "template-rocq";

  metarocq_ = package: let
      metarocq-deps = if package == "single" then []
        else map metarocq_ (head (splitList (pred.equal package) packages));
      pkgpath = if package == "single" then "./" else "./${package}";
      pname = if package == "all" then "metarocq" else "metarocq-${package}";
      pkgallMake = ''
          mkdir all
          echo "all:" > all/Makefile
          echo "install:" >> all/Makefile
        '' ;
      derivation = (mkCoqDerivation ({
        inherit version pname defaultVersion release releaseRev repo owner;

        mlPlugin = true;
        propagatedBuildInputs = [ equations coq.ocamlPackages.zarith ] ++ metarocq-deps;

        patchPhase =  ''
          patchShebangs ./configure.sh
          patchShebangs ./template-rocq/update_plugin.sh
          patchShebangs ./template-rocq/gen-src/to-lower.sh
          patchShebangs ./safechecker-plugin/clean_extraction.sh
          patchShebangs ./erasure-plugin/clean_extraction.sh
          echo "CAMLFLAGS+=-w -60 # Unused module" >> ./safechecker/Makefile.plugin.local
          sed -i -e 's/mv $i $newi;/mv $i tmp; mv tmp $newi;/' ./template-rocq/gen-src/to-lower.sh ./safechecker-plugin/clean_extraction.sh ./erasure-plugin/clean_extraction.sh
        '' ;

        configurePhase = optionalString (package == "all") pkgallMake + ''
          touch ${pkgpath}/metarocq-config
        '' + optionalString (elem package ["safechecker" "erasure" "template-pcuic" "quotation" "safechecker-plugin" "erasure-plugin"]) ''
          echo  "-I ${template-rocq}/lib/coq/${coq.coq-version}/user-contrib/MetaRocq/Template/" > ${pkgpath}/metarocq-config
        '' + optionalString (package == "single") ''
          ./configure.sh local
        '';

        preBuild = ''
          cd ${pkgpath}
        '' ;

        meta = {
          homepage    = "https://metarocq.github.io/";
          license     = licenses.mit;
          maintainers = with maintainers; [ cohencyril ];
        };
      } // optionalAttrs (package != "single")
        { passthru = genAttrs packages metarocq_; })
     ).overrideAttrs (o:
       let requiresOcamlStdlibShims = versionAtLeast o.version "1.0-8.16" ||
                                      (o.version == "dev" && (versionAtLeast coq.coq-version "8.16" || coq.coq-version == "dev")) ;
       in
       {
         propagatedBuildInputs = o.propagatedBuildInputs ++ optional requiresOcamlStdlibShims coq.ocamlPackages.stdlib-shims;
       });
    in derivation;
in
metarocq_ (if single then "single" else "all")
