# Inventory

Every file of the delivery, with size and SHA-256 (also in `SHA256SUMS`; check with `sha256sum -c SHA256SUMS`). Excluded: `.lake/` (regenerable build products and dependency checkouts) and `.git/`. No credentials are included.

| File | Bytes | SHA-256 | Description |
|---|---|---|---|
| `.github/workflows/ci.yml` | 1959 | `ead74d0f8b08d93ca25cd1e324b65af5e2ec552f272a04192b91082c3df96567` |  |
| `.gitignore` | 24 | `3074d3d974b5f9de1e7fb9a9bba43b35b70d1a4a54d837c35420109e5d533985` |  |
| `AGENTS.md` | 4648 | `83fecffb1d60d7fa149eca65111332e36978270a0dda0c735b1f27606074f47d` | rules and workflow for agents and reviewers |
| `CHECKPOINT.md` | 4080 | `e06c2d763410e22c472fb9dd3441626005cbc1db329ff7a5015aee47c0f769b9` | current state and remaining work |
| `Challenge.lean` | 39203 | `aeb2634c1de95b9177f2e8676eb75ac99a8d73bae374d105f34737a9bfbeb606` | statement file: 70 compared statements (sorry), definitions copied from the library |
| `LICENSE` | 11357 | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` | Apache-2.0 licence text |
| `MosaicSpaces/Abstract.lean` | 12564 | `44a36f67801f4917e5d8324d8d047787604882866a3f477444c5d7e4d6951f34` |  |
| `MosaicSpaces/Answers.lean` | 14415 | `fd9de70c2eed5910120409d7f4995d21879a2355e9ec75310a06f398687a82f3` |  |
| `MosaicSpaces/Arc/Minimal.lean` | 8355 | `e0c8c0e506c4b26a6d7ae5d4d034ac7d2b53d9f5642ae935ae0b1a0e54a3712b` |  |
| `MosaicSpaces/Arc/Param.lean` | 19346 | `cc90af4f2b1b2ef628dd067476ca99fe29fd852c5213074e7bbef535ed649f60` |  |
| `MosaicSpaces/ArcConsequences.lean` | 5156 | `bded3e55e7862e97d045d02ade67a9e891f95c9d35defcb3430c2c89be71213e` |  |
| `MosaicSpaces/Classes.lean` | 12186 | `e61e155c39a603b2bbd754c3d1a8a72db7c8da4440083158a27548d968b904cb` |  |
| `MosaicSpaces/Classical/Bump.lean` | 2834 | `5c1dce7d69f3d4fc2c2e8e638fc039bb15286a9437ec22d90237d99a1cf08428` |  |
| `MosaicSpaces/Cone.lean` | 26381 | `26f6390052afe44fdf47fd3a20457898555fe558f82fa23438b262b88d5c4eeb` |  |
| `MosaicSpaces/Cone4.lean` | 14288 | `16069a7f087e9ec264dfcb93fcd90e02d4561846131cc376b1f9aef6149bcdca` |  |
| `MosaicSpaces/Continua.lean` | 11744 | `c8f5b7138aca927ba367ab8ec3fb00186dc787153fd88dde46fb34e52bbabdda` |  |
| `MosaicSpaces/Fan.lean` | 15795 | `f9eaea9e7241b65f7c42446b3b499d654ee329d0847ade682298724c851288a6` |  |
| `MosaicSpaces/FanMetric.lean` | 13506 | `a17d76f9dc7c08e4f86b55b4114997a69d406e3013ff02c169edc8734e49466b` |  |
| `MosaicSpaces/FirstCountable.lean` | 16735 | `2ec044082cf4c6356253bd2b5022c87fcc0feaf19162ca88e88d4215cf501340` |  |
| `MosaicSpaces/G/Basic.lean` | 28336 | `e982f8533a44795f674741caf82d86cd934d6e1f06c90ecc4d61c51c6272ad14` |  |
| `MosaicSpaces/G/Capture.lean` | 18175 | `c28556ca1f5f6a7df777bb619fcd0df7164eca6e8679f2bb93cdd753404ad9af` |  |
| `MosaicSpaces/G/Mosaic.lean` | 18042 | `8f550e7da7da899810cf95d283317e54074b1568c91bb10440d3745ae9b6d4bb` |  |
| `MosaicSpaces/G/Remarks.lean` | 7906 | `78df49d549082e6fd16e5ce415a6b9bbef0b6341048ffe648be015ed03edf107` |  |
| `MosaicSpaces/G/Tychonoff.lean` | 35094 | `62119b1d4c06716cc54a66b5749c9c5de991ba2573ca5ca4462b74b1af4a9fed` |  |
| `MosaicSpaces/Image.lean` | 9330 | `8213bb6e9b54aa85f20cd0cd0d7e21a822200c60c7f7a2cc59567d70c461fc25` |  |
| `MosaicSpaces/Local.lean` | 11753 | `eee7757bb606407c35e25bd876906bac4063411d37c147fd09146eda7a6e06d4` |  |
| `MosaicSpaces/Mosaic.lean` | 15225 | `32fe3a5878766fa22965399e9a101d2a462897df03046ee06c4281aab61456a3` |  |
| `MosaicSpaces/PathComponents.lean` | 4242 | `bc96bbffb08b995f6b290ac5e69eef1739b284e82ed0559175861bfa23563dac` |  |
| `MosaicSpaces/PathDetermined.lean` | 7190 | `47171c4135fcab6f6d6a202443e980521dc1c920d5af2ffbc418a7331c3f6c44` |  |
| `MosaicSpaces/Peano/Chain.lean` | 4131 | `0c0a9b7fb4c810393c5741cbd927d5e20af299a6502b236041cae514fa603f20` |  |
| `MosaicSpaces/Peano/Consequences.lean` | 10759 | `9031c3f285cd247452abe99b312c7543471ba9c9383f9a3997b818d70a7bfccc` |  |
| `MosaicSpaces/Peano/LPC.lean` | 3417 | `1556cad2a3a8a87b6b75888f494fd2bd5ad540ae4e5d6ffc16a416f7c863b903` |  |
| `MosaicSpaces/Peano/Path.lean` | 13084 | `1a4312f229b34bf1f19d48d54a8a8ed2237022759106c451b3347c81a98b87a9` |  |
| `MosaicSpaces.lean` | 1014 | `ae737abc00eb0b725f7f8676e69a935f3b98a44f881552e9cd50cc20d717bf5c` | library root module |
| `README.md` | 6580 | `a3e0bc683d6cd07b684f6fd5654060ba12d6eb628764f876c6f511852079373b` | overview, status, AI disclosure |
| `Solution.lean` | 20850 | `6dbc380f6851f4c27d31399e85fb2c26becbbdd27fae31cba9ec66326de27c09` | proofs of the 70 statements from the library |
| `article/mosaic_article.tex` | 115796 | `4fa533f0b12af1a9668fa3f0f196ada8bc58778b3de3d88e86108da095804ca7` | the article |
| `comparator.json` | 3036 | `a2ada95794b1523c9011ba52a0c3eb5e546e2c86bf81204e4b7043c82f558258` | Comparator configuration |
| `docs/ARCHITECTURE.md` | 9051 | `d60019251d85ef3f6f8caf96df1290ad0d3673200046577c06cc90b5abaf06d6` |  |
| `docs/ARTICLE_AUDIT.md` | 9413 | `950122b1bb17b307181a762a3da0cf91c3493e61d0568dc48c453e12c40495fb` |  |
| `docs/COVERAGE_LEDGER.md` | 34923 | `61e5c112584501be66a90989b15e4d843910a261a305af1ed1c6243b01b7d119` | coverage ledger (generated) |
| `docs/MATHLIB_GAPS.md` | 4632 | `4a9f691c442e5bbbfd4b826771be5862d97996e475fe888f21962dc18b5e5753` |  |
| `docs/PALOMAR_REQUIREMENTS.md` | 9519 | `232c87f75107047c932f6dab2ee88e1497d2cdbb80fedbace238286abdf1ebf1` |  |
| `docs/PUSH_AND_SUBMIT.md` | 2348 | `454ccbf141230c8479f520668e9ded14e1a6962e4473a73b01b193a0111c4d66` |  |
| `docs/VERIFICATION_PLAN.md` | 3016 | `3711200062c87b20c696875306276f7b2303c3be30ab1887790c4b5da195ac46` |  |
| `formalization.yaml` | 18409 | `580ba0d5fa4885058fbc3fa43f28f3e87c527e2aa5fca60ad77e62bf62a9eb05` | Palomar metadata (CONFIRM fields to be confirmed by the author) |
| `lake-manifest.json` | 3236 | `bce7bda3d44be12f16c29a72cb820e5f7ff47b2154b0bc30ccb51538573ba559` | dependency pins |
| `lakefile.toml` | 396 | `f7056ee289881e320d0784eed52fea9244747c4f08dfc37959996b7f697e2a79` | the only Lake configuration |
| `lean-toolchain` | 29 | `8dc8d6f560141069d9073e370611716ef77ada0da8ffa37e2149f44b2e63ac7a` | Lean toolchain pin |
| `ledger/build_ledger.py` | 48156 | `3a136ca7206ed05c8b2835407b270b94dfc4d3b7fc7c58983791cb5bc1c83c94` | ledger source |
| `ledger/coverage.json` | 48672 | `18abe7a71c661892cf13cc6db76b06bcd17b507a4ebaeddb47d39ee605015c82` | coverage ledger (generated, JSON) |
| `logs/environment_probe.log` | 2402 | `87f10ca099cbe8ba98e1867cd70914352bdc4195f4bedad47a947b515ca892dd` | verification log |
| `logs/superseded/README.md` | 278 | `eb4a55c878bb39842ae813b12563049b48e5e6770e0079e8b29b0bcd7eeb3de0` | verification log |
| `logs/superseded/axioms.log` | 5207 | `267a5a302a8f26dcc4fa8709d27d4d93a4e046fcac467476cb0c6a6d51f13ece` | verification log |
| `logs/superseded/comparator-negative-definition.log` | 35705 | `2c5a5b194918d33a6622ac39f2bfac91a0d7ac1e8da11342bfc2b51a78c3ce76` | verification log |
| `logs/superseded/comparator-negative-sorry.log` | 35706 | `e5eeec7a5b22e0a8253fa319606b325668f28696abcaf932fbc2c8afae936004` | verification log |
| `logs/superseded/comparator-negative-statement.log` | 35706 | `0a540b9ab7949433b9c593db162bd99c464d43438d3a8375f45cd2ba093ec316` | verification log |
| `logs/superseded/comparator-nosandbox.log` | 35790 | `8c687faad05f012930ae572032a610fb67662924976ac271c0e4cff51516c770` | verification log |
| `logs/superseded/comparator-paranoid-nosandbox.log` | 36614 | `82b9d7d476251488c0d3d6f70315f4a66674bb989540e134f9b7a3505e983f1b` | verification log |
| `logs/superseded/verify-20261117T061636Z/00-sources.log` | 129 | `b5243fd2f7c9cb38b7a84bdcdccae023e7b2a90903721881db05bd0baea68660` | verification log |
| `logs/superseded/verify-20261117T061636Z/01-build-challenge.log` | 1873 | `1f69e5e7d18312222ed35e819dd4f711eb842204074891b316a99888df327c5f` | verification log |
| `logs/superseded/verify-20261117T061636Z/01-build.log` | 30887 | `84b79c4eac7c0a661c86158cce91fa4bc909edc5ffa78d54a45494295f87cd28` | verification log |
| `logs/superseded/verify-20261117T061636Z/01-clean.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | verification log |
| `logs/superseded/verify-20261117T061636Z/02-axioms-check.log` | 111 | `0b480d59118a76b4c3440b0b84b09ea300e0fd67b9871f69885e721f42374de4` | verification log |
| `logs/superseded/verify-20261117T061636Z/02-axioms-print.log` | 5207 | `32d025c24d3ed6637904742f00378c62459958aedce1e9f59c6705ea2683d92c` | verification log |
| `logs/superseded/verify-20261117T061636Z/03-comparator-NOSANDBOX.log` | 35746 | `7b443ca97540a1ef3f413acc7f1712d680d7047f3b3c94f0774d2813457b7370` | verification log |
| `logs/superseded/verify-20261117T061636Z/04-check-NOSANDBOX.log` | 30947 | `ba512df15c3a0ebe4b29dde4134117ed55bdf4542aa98e8cdda2ef6cd510662f` | verification log |
| `logs/superseded/verify-20261117T061636Z/05-check-paranoid-NOSANDBOX.log` | 34692 | `8d573d379f7b5f6cba90787b9d9a76292bb64af43a233c4883bea4e5dd44c918` | verification log |
| `logs/superseded/verify-20261117T061636Z/06-comparator-paranoid-NOSANDBOX.log` | 36570 | `860fd61e9fe06b95e433a78aa5187e261d6500a865a9292646c864e2448c2b09` | verification log |
| `logs/superseded/verify-20261117T061636Z/07-palomar-local-NOSANDBOX.log` | 36027 | `7cae0e3aad309ee45514773ba6f304de185a7df7b09ac47f34e5d0166ea554ab` | verification log |
| `logs/superseded/verify-20261117T061636Z/08-negative-sorry-NOSANDBOX.log` | 35706 | `ecfe295939f159a1be9305c00c145b323096536298f089b55148bec56bb59fea` | verification log |
| `logs/superseded/verify-20261117T061636Z/09-negative-definition-NOSANDBOX.log` | 35705 | `07c3998e40c56f78987587d0c09c0ad070df8a31b3dbcba524539bf22df769ea` | verification log |
| `logs/superseded/verify-20261117T061636Z/provenance.txt` | 1268 | `97ff19513f54156ac8b6344e0cf8adc1887ebdbe69de8e0b50dc6f0190321f09` | verification log |
| `logs/superseded/verify-20261117T061636Z/steps.tsv` | 1387 | `49ad16a2ec220798820e4f91f19e47d91e069fb0c0ac64731b7690f72e13c873` | verification log |
| `logs/verify-20261117T144600Z/00-sources.log` | 129 | `c9563d2e4a690bdda3fd8bfca3b29434f7a63382799aad5a7e1057e76b54ba21` | verification log |
| `logs/verify-20261117T144600Z/01-build-challenge.log` | 4345 | `500de45c04fa0dc347219e11a3ec53fae4f6307ded9208ed2757b23f48e6acf6` | verification log |
| `logs/verify-20261117T144600Z/01-build.log` | 50895 | `3124fcf19f1b54b9a7e31f30d45e49fd180b03e8a3fdebae49e1040c69083208` | verification log |
| `logs/verify-20261117T144600Z/01-clean.log` | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | verification log |
| `logs/verify-20261117T144600Z/02-axioms-check.log` | 113 | `b5a4742f918c73ec19bd411650ec87086b7e945a74bdfc963d3160aebdaa807e` | verification log |
| `logs/verify-20261117T144600Z/02-axioms-print.log` | 13000 | `28e942758bea16c7d5f9c8493a7112bb058082065d5278a2ea62666e539df2d0` | verification log |
| `logs/verify-20261117T144600Z/03-comparator-NOSANDBOX.log` | 60424 | `46fe4beb744d2eca642fbcdc2fe9ce041d335eb9701decfc9d3ecf2079727245` | verification log |
| `logs/verify-20261117T144600Z/04-check-NOSANDBOX.log` | 50493 | `be24b00cc5938cc582e3325290756990927732a433c3681292108d593cc1e470` | verification log |
| `logs/verify-20261117T144600Z/05-check-paranoid-NOSANDBOX.log` | 54631 | `b488d3e6d0e4443aa60a3b8b54ea5eae905c8986e742d88fee64b9ec11b972d9` | verification log |
| `logs/verify-20261117T144600Z/06-comparator-paranoid-NOSANDBOX.log` | 61248 | `6f433c8b857a463abcdb17d96bedf14bea95d1931db31241a6ba2535b655878a` | verification log |
| `logs/verify-20261117T144600Z/07-palomar-local-NOSANDBOX.log` | 60705 | `573d705ce8ff3d855d2b7b889f7d50811e96aff86f02a494f1e6064604f4da14` | verification log |
| `logs/verify-20261117T144600Z/08-negative-sorry-NOSANDBOX.log` | 60384 | `fdf7e945fac0a6d7d857c841808590967928d1099b9c5e4c15b82b588639c933` | verification log |
| `logs/verify-20261117T144600Z/09-negative-definition-NOSANDBOX.log` | 60383 | `74b24ac50ef507e127c49f5ff8891774843e395ba134a18af3e2b11bf8fe81a0` | verification log |
| `logs/verify-20261117T144600Z/provenance.txt` | 1268 | `1c0b7e0572a77ce9e4e90511cd44c3373fa4fb614a81b439bbfe1f6084459e0f` | verification log |
| `logs/verify-20261117T144600Z/steps.tsv` | 1388 | `b6fb38bb52def423a1579b588af5b717976cb3e487572b084a50679630b5c7f5` | verification log |
| `logs/verify_all.stdout` | 3160 | `13da44cfa1883d771dbe69ce2c8976cbea235350c330a4beb92111af459ae826` | verification log |
| `reports/ai_adversarial_review.md` | 22520 | `47013b8cf634f0f2284f950d0419762eb4e92c5fddef8dd58be40736e9db333e` | review by a separate AI agent, with responses |
| `reports/make_summary.py` | 7946 | `8b8f1b4dd25178386150b45c82767d7d919019b058ee73bced0a70dc3920b0e5` |  |
| `reports/summary.json` | 8163 | `d1b8cd2fb787c3768623d7e36e6e400c28ed3579c3002f0668ed36cd58193c65` | machine-readable summary |
| `reports/verification_report.md` | 7965 | `786f052d92b7e4938b0fbde4d7adccc42b88a4e835deb35dae1670798a9e7f90` | human-readable verification report |
| `sandbox/Containerfile` | 646 | `61a0187806a796743e324cd85ea2a7ba4d51d41ad4fa7c82331d13ccd6490528` |  |
| `sandbox/README.md` | 2235 | `ff2458ba1ede1aa4a37e4591808e635d9c5ff991a3cd7f818a018ac9340298b9` |  |
| `sandbox/run.sh` | 768 | `e5cdbc963331bd003e105bfdbc8ade7ea70cbe43fe0c45e73bd5d03dec2ea33f` |  |
| `scripts/axioms.lean` | 6794 | `5fd7c45db6a84e3f6241b07917f040494fcad21ad0f4f2fdf8c0c492c67c8ac4` |  |
| `scripts/check_axioms.py` | 899 | `8b0f7d3f77bb20184062404cebddf77120e2eda4e7a933189a43b1512a891cda` |  |
| `scripts/check_sources.py` | 3879 | `125c052b36ebce379ab40f18386a0e3e41394f514dee0a2796ed22ead9402a98` |  |
| `scripts/make_inventory.py` | 2751 | `89a6d172efe593608cbcab0216c244de7f47dd0cc01a2113819ee894205fb285` |  |
| `scripts/verify_all.sh` | 7751 | `167b865c2337af930175c78fde434b68b9fadac9ee7b1e1d7791f01fe23bb57a` | runs all checks and negative controls |
| `watch.ps1` | 3122 | `cba80a6b9dfd5616f3a2c7253ed53e8db6dd968d7545551c34cf9d0a801e41fd` |  |
