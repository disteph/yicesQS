(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Benchmarks generated by the Calysto static checker.  Provided by Domagoj
Babic.  See http://www.cs.ubc.ca/~babic/index_benchmarks.htm.  Translated using
Spear Sf2Smt translator.

|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun v28291760 () (_ BitVec 32))
(declare-fun o33377328 () (_ BitVec 1))
(declare-fun v29788568 () (_ BitVec 64))
(declare-fun o55952224 () (_ BitVec 1))
(declare-fun v27776316 () (_ BitVec 32))
(declare-fun v19621104 () (_ BitVec 64))
(declare-fun o26760012 () (_ BitVec 1))
(declare-fun v26296828 () (_ BitVec 32))
(declare-fun v28256836 () (_ BitVec 32))
(declare-fun o41990576 () (_ BitVec 64))
(declare-fun o41519088 () (_ BitVec 1))
(declare-fun o70337432 () (_ BitVec 32))
(declare-fun o49235492 () (_ BitVec 32))
(declare-fun o41888664 () (_ BitVec 1))
(declare-fun v38553168 () (_ BitVec 32))
(declare-fun o30466136 () (_ BitVec 32))
(declare-fun o27269816 () (_ BitVec 32))
(declare-fun o46358076 () (_ BitVec 32))
(declare-fun o35236612 () (_ BitVec 1))
(declare-fun v43938036 () (_ BitVec 64))
(declare-fun v26878532 () (_ BitVec 64))
(declare-fun o35505344 () (_ BitVec 64))
(declare-fun o28028344 () (_ BitVec 64))
(declare-fun o31432428 () (_ BitVec 1))
(declare-fun o34735032 () (_ BitVec 1))
(declare-fun v38148380 () (_ BitVec 64))
(declare-fun o33291888 () (_ BitVec 1))
(declare-fun o28347996 () (_ BitVec 1))
(declare-fun v18855352 () (_ BitVec 1))
(declare-fun o31772592 () (_ BitVec 1))
(declare-fun o42875936 () (_ BitVec 1))
(declare-fun v33268532 () (_ BitVec 1))
(declare-fun o51283052 () (_ BitVec 1))
(declare-fun o22723584 () (_ BitVec 64))
(declare-fun v25064812 () (_ BitVec 64))
(declare-fun o22543552 () (_ BitVec 64))
(declare-fun v27933168 () (_ BitVec 32))
(declare-fun o21589916 () (_ BitVec 64))
(declare-fun o56392412 () (_ BitVec 1))
(declare-fun o29904504 () (_ BitVec 1))
(declare-fun o52939840 () (_ BitVec 1))
(declare-fun o25537100 () (_ BitVec 1))
(declare-fun o30305152 () (_ BitVec 1))
(declare-fun o20781556 () (_ BitVec 1))
(declare-fun o22177580 () (_ BitVec 1))
(declare-fun o32057376 () (_ BitVec 1))
(declare-fun o46134236 () (_ BitVec 1))
(declare-fun o19276408 () (_ BitVec 1))
(declare-fun o38289572 () (_ BitVec 1))
(declare-fun o23153004 () (_ BitVec 1))
(declare-fun o24477416 () (_ BitVec 1))
(declare-fun o22514360 () (_ BitVec 1))
(declare-fun o47158032 () (_ BitVec 1))
(declare-fun o32519984 () (_ BitVec 1))
(declare-fun o24524524 () (_ BitVec 1))
(declare-fun o50764220 () (_ BitVec 1))
(declare-fun o31344616 () (_ BitVec 1))
(declare-fun o25436988 () (_ BitVec 1))
(declare-fun v70367096 () (_ BitVec 64))
(declare-fun v50086324 () (_ BitVec 64))
(declare-fun o50770804 () (_ BitVec 64))
(declare-fun o46114872 () (_ BitVec 32))
(declare-fun o29857300 () (_ BitVec 64))
(declare-fun o31808672 () (_ BitVec 64))
(declare-fun v43016368 () (_ BitVec 64))
(declare-fun o22138668 () (_ BitVec 64))
(declare-fun o38068656 () (_ BitVec 64))
(declare-fun o28805820 () (_ BitVec 64))
(declare-fun o28788340 () (_ BitVec 64))
(declare-fun o47729876 () (_ BitVec 1))
(declare-fun o18914128 () (_ BitVec 1))
(declare-fun v28294628 () (_ BitVec 32))
(declare-fun o26740284 () (_ BitVec 1))
(declare-fun o24324932 () (_ BitVec 1))
(declare-fun v36198720 () (_ BitVec 32))
(declare-fun v62394888 () (_ BitVec 32))
(declare-fun o34436044 () (_ BitVec 32))
(declare-fun o27130848 () (_ BitVec 32))
(declare-fun v25786800 () (_ BitVec 32))
(declare-fun o24356004 () (_ BitVec 32))
(declare-fun o18975444 () (_ BitVec 1))
(declare-fun o34621888 () (_ BitVec 1))
(declare-fun Fresh__0 () (_ BitVec 1))
(declare-fun Fresh__1 () (_ BitVec 1))
(declare-fun Fresh__2 () (_ BitVec 1))
(declare-fun Fresh__3 () (_ BitVec 1))
(declare-fun Fresh__4 () (_ BitVec 1))
(declare-fun Fresh__5 () (_ BitVec 1))
(declare-fun Fresh__6 () (_ BitVec 1))
(declare-fun Fresh__7 () (_ BitVec 1))
(declare-fun Fresh__8 () (_ BitVec 1))
(declare-fun Fresh__9 () (_ BitVec 1))
(declare-fun Fresh__10 () (_ BitVec 1))
(declare-fun Fresh__11 () (_ BitVec 1))
(declare-fun Fresh__12 () (_ BitVec 1))
(declare-fun Fresh__13 () (_ BitVec 1))
(declare-fun Fresh__14 () (_ BitVec 1))
(declare-fun Fresh__15 () (_ BitVec 1))
(declare-fun Fresh__16 () (_ BitVec 1))
(declare-fun Fresh__17 () (_ BitVec 1))
(declare-fun Fresh__18 () (_ BitVec 1))
(assert (= (= Fresh__0 (_ bv1 1)) (= v28291760 ((_ extract 31 0) (_ bv0 64)))))
(assert (= o33377328 Fresh__0))
(assert (= (= Fresh__1 (_ bv1 1)) (bvslt v29788568 ((_ extract 63 0) (_ bv0 64)))))
(assert (= o55952224 Fresh__1))
(assert (= (= Fresh__2 (_ bv1 1)) (bvslt v19621104 ((_ extract 63 0) (_ bv0 64)))))
(assert (= o26760012 Fresh__2))
(assert (= o41990576 ((_ sign_extend 32) v28256836)))
(assert (= (= Fresh__3 (_ bv1 1)) (bvult v19621104 o41990576)))
(assert (= o41519088 Fresh__3))
(assert (= o70337432 (ite (= o41519088 (_ bv1 1)) ((_ extract 31 0) (_ bv18446744073709551615 64)) ((_ extract 31 0) (_ bv0 64)))))
(assert (= o49235492 (ite (= o26760012 (_ bv1 1)) v26296828 o70337432)))
(assert (= (= Fresh__4 (_ bv1 1)) (bvslt o49235492 ((_ extract 31 0) (_ bv0 64)))))
(assert (= o41888664 Fresh__4))
(assert (= o30466136 (ite (= o41888664 (_ bv1 1)) ((_ extract 31 0) (_ bv0 64)) v38553168)))
(assert (= o27269816 (ite (= o55952224 (_ bv1 1)) v27776316 o30466136)))
(assert (= o46358076 (ite (= o33377328 (_ bv1 1)) o27269816 v28291760)))
(assert (= (= Fresh__5 (_ bv1 1)) (distinct ((_ extract 31 0) (_ bv0 64)) o46358076)))
(assert (= o35236612 Fresh__5))
(assert (= o35505344 (bvsrem v26878532 o41990576)))
(assert (= o28028344 (bvsub v26878532 o35505344)))
(assert (= (= Fresh__6 (_ bv1 1)) (bvsle v43938036 o28028344)))
(assert (= o31432428 Fresh__6))
(assert (= o34735032 (bvand o31432428 ((_ extract 0 0) (_ bv1 64)))))
(assert (= (= Fresh__7 (_ bv1 1)) (bvslt o28028344 v38148380)))
(assert (= o33291888 Fresh__7))
(assert (= o28347996 (bvand o34735032 o33291888)))
(assert (= (= Fresh__8 (_ bv1 1)) (distinct ((_ extract 31 0) (_ bv0 64)) v38553168)))
(assert (= o31772592 Fresh__8))
(assert (= o42875936 (bvand o31772592 ((_ extract 0 0) (_ bv1 64)))))
(assert (= o51283052 (ite (= v18855352 (_ bv1 1)) o42875936 v33268532)))
(assert (= o22723584 (bvsub o28028344 v43938036)))
(assert (= o22543552 (bvudiv o22723584 v25064812)))
(assert (= o21589916 ((_ sign_extend 32) v27933168)))
(assert (= (= Fresh__9 (_ bv1 1)) (bvult o22543552 o21589916)))
(assert (= o56392412 Fresh__9))
(assert (= o29904504 (bvand o28347996 o56392412)))
(assert (= o52939840 (bvand o29904504 o33377328)))
(assert (= o25537100 (bvand o51283052 o52939840)))
(assert (= (= Fresh__10 (_ bv1 1)) (bvsle ((_ extract 63 0) (_ bv0 64)) v19621104)))
(assert (= o30305152 Fresh__10))
(assert (= o20781556 (bvand ((_ extract 0 0) (_ bv1 64)) o30305152)))
(assert (= (= Fresh__11 (_ bv1 1)) (bvule o41990576 v19621104)))
(assert (= o22177580 Fresh__11))
(assert (= o32057376 (bvand o22177580 o20781556)))
(assert (= o46134236 (ite (= o41519088 (_ bv1 1)) o20781556 o32057376)))
(assert (= o19276408 (ite (= o26760012 (_ bv1 1)) ((_ extract 0 0) (_ bv1 64)) o46134236)))
(assert (= (= Fresh__12 (_ bv1 1)) (bvsle ((_ extract 63 0) (_ bv0 64)) v29788568)))
(assert (= o38289572 Fresh__12))
(assert (= o23153004 (bvand o38289572 o25537100)))
(assert (= o24477416 (bvand o19276408 o23153004)))
(assert (= (= Fresh__13 (_ bv1 1)) (bvsle ((_ extract 31 0) (_ bv0 64)) o49235492)))
(assert (= o22514360 Fresh__13))
(assert (= o47158032 (bvand o22514360 o24477416)))
(assert (= o32519984 (ite (= o41888664 (_ bv1 1)) o24477416 o47158032)))
(assert (= o24524524 (ite (= o55952224 (_ bv1 1)) o25537100 o32519984)))
(assert (= o50764220 (ite (= o33377328 (_ bv1 1)) o24524524 o29904504)))
(assert (= o31344616 (bvand o28347996 o50764220)))
(assert (= o25436988 (bvand o35236612 o31344616)))
(assert (= o50770804 (ite (= o41888664 (_ bv1 1)) ((_ extract 63 0) (_ bv0 64)) v50086324)))
(assert (= o46114872 ((_ extract 31 0) o50770804)))
(assert (= o29857300 ((_ sign_extend 32) o46114872)))
(assert (= o31808672 (ite (= o55952224 (_ bv1 1)) v70367096 o29857300)))
(assert (= o22138668 (ite (= o33377328 (_ bv1 1)) o31808672 v43016368)))
(assert (= o38068656 (bvsub o28028344 o22138668)))
(assert (= o28805820 (bvsdiv o38068656 o41990576)))
(assert (= o28788340 (bvsdiv o28805820 ((_ extract 63 0) (_ bv8 64)))))
(assert (= (= Fresh__14 (_ bv1 1)) (bvult o28788340 o41990576)))
(assert (= o47729876 Fresh__14))
(assert (= o18914128 (bvand o25436988 o47729876)))
(assert (= (= Fresh__15 (_ bv1 1)) (= v28294628 ((_ extract 31 0) (_ bv0 64)))))
(assert (= o26740284 Fresh__15))
(assert (= o24324932 (bvand o18914128 o26740284)))
(assert (= o34436044 (ite (= o41888664 (_ bv1 1)) ((_ extract 31 0) (_ bv0 64)) v62394888)))
(assert (= o27130848 (ite (= o55952224 (_ bv1 1)) v36198720 o34436044)))
(assert (= o24356004 (ite (= o33377328 (_ bv1 1)) o27130848 v25786800)))
(assert (= (= Fresh__16 (_ bv1 1)) (distinct ((_ extract 31 0) (_ bv0 64)) o24356004)))
(assert (= o18975444 Fresh__16))
(assert (= (= Fresh__17 (_ bv1 1)) (=> (= o24324932 (_ bv1 1)) (= o18975444 (_ bv1 1)))))
(assert (= o34621888 Fresh__17))
(assert (= (= Fresh__18 (_ bv1 1)) (= ((_ extract 0 0) (_ bv0 64)) o34621888)))
(assert (= (_ bv1 1) Fresh__18))
(check-sat)
(exit)
