import YM.TraceExtension.Weir.Amen
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{x A a C D:ℝ} {k:ℕ}{S:Stage}{f:Peat G n}{R:Rep G n}{J:Dart G n}
lemma Snow.raise (h:Snow R f x a)(he:a≤ A): Snow R f x A:=⟨h.regular,h.fare.1.trans he,fun u hU i hv hp=>(h.fare.2 u hU i hv hp).trans he⟩
lemma ClimateJ.plus(h:ClimateJ R f x a C)(hp:a≤A)(he:C≤D):ClimateJ R f x A D:=⟨h.silk,h.puff.raise hp,fun u=>(h.price u).trans he⟩
lemma Snow.scale(h:Snow R f x A)(v:ℝ): Snow R (v • f) x (|v| * A):=by
    let p:=R.p;let Q:=tempQ x (n:=n);let F:=v • f
    have ht(U)(hh:Healthy p.threshold Q U): Clear p.order (p.dirBound (0:Site n)) U F (|v| * A):= (⟨h.1.4 U hh,h.fare.2 U hh⟩: Clear p.order _ U f A).scale v
    exact ⟨⟨fun U V hv=> congr_arg (v •·) (h.1.1 U V hv), h.1.2.const_smul v,fun k U=> congr_arg (v • ·) (h.1.3 k U), fun U hh=> (ht U hh).wake,fun U hh w _ hl=> Next.Foundations.left_has w hl (ht U hh).wake⟩,mul_nonneg (abs_nonneg _) h.fare.1,fun U hh=>(ht U hh).pay ⟩
abbrev kerr(x:ℝ)(m:ℕ)(Y:Gal G n)(F:Peat G n): Peat G n:= (peace x)⁻¹ • atuneU m Y F (peace x) (ExtS n x)
lemma caskCover(m:ℕ)(T:Collar G S.order)(x:ℝ)(he:1≤x)(Λ D:ℝ)(R:Rep G n){X:Gal G n} {F:Peat G n} (H: Castle m S.order X F x R S D (Cube.fee T))(hp:Age S x Λ R)(hv:Cube.Wire R.p (high x) (hp.rank.symm ▸ T))(hn:20*(high x+10)< n.val) : Snow R (kerr x m X F) x (composeCost S.order (swole x) (Cube.fee T)):=by
    let p:=R.p; let T':Collar G p.order:=hp.rank.symm ▸ T; have ht:= fees_eq T hp.rank.symm; let u:= atuneU m X F (peace x) (ExtS n x); let c:=swole x; let a':=composeCost S.order c (Cube.fee T); let q:=peace x; have hq: 0< q:=(pet x he S).2.1
    have Hz : Snow R u x (composeCost S.order (c*q) (Cube.fee T)):=by
        let P:=tempQ x (n:=n); have hG:= H.reg _ ((dec_b ..).2); have hτ:0 ≤ swole x:=by unfold swole; positivity
        have hc:= H.reg (ExtS n x) (fun _ h=>h)
        refine ⟨hG,?_⟩; let f(x':Directions G n)(ha:‖x'‖≤ Cube.fee T'):Through p.order (minor u (Cube.moduleBill p (high x))) x' (c*q):=by rw[← shifts x S Λ R hp,hp.rank]; exact H.pay x' (ht ▸ ha)
        have hC:p.supBounds 0 P u (composeCost p.order (c*q) (Cube.fee T')):= lends (r:=high x) hG (fun _ h=>h) hc.sites (by omega) T' hv (mul_nonneg hτ hq.le) f; rw[ht,show p.order=S.order from hp.rank] at hC; exact hC
    have hl:= Hz.scale q⁻¹; convert hl using 1; unfold composeCost; rw [abs_of_pos (inv_pos.mpr hq)]; unfold q c; field_simp [(show peace x≠0 from hq.ne')]; rw[mul_div_cancel_right₀ _ (Zn.wake ..).ne']
lemma medal(G:Gauge)(h:G.Simple)(S:Stage)(k:ℕ)(C M:ℝ)(hp:G.colorScale ≤ C)(V:Type)(n:Side)(R:Rep G n)(J:Dart G n)(x:ℝ)(hf:Craft S x R J k C)(b:Axis) : HearthV (stubJ (lush (YCore x J b))) (Bay n x) k (2*thinM x) C:=by
    let F:=YCore x J b; have he:=hf.cloud b
    refine ⟨lush_p he h,fun u v hm=> congr_arg₂ (·-·) (lushLocales he u v hm) rfl,fun j U=> congr_arg₂ (· - ·) (lushSym he j U) rfl,hf.jack b,fun X _ _ W y hz=> ?_⟩
    have ht: |lush F 1|≤thinM x:= (hf.jump b X (fun _=>1) y (fun i=>allows_const y ((SectorAffine.mat_paid ( (1:Config G n) i)).le.trans hp))).value;
    rw[two_mul]; exact (hf.jump b X W y hz).add (allows_const y (show ‖-lush F 1‖ ≤ thinM x from (norm_neg _).trans_le ht))
variable (T: Collar G S.order)
structure Wealth (S:Stage)(R:Rep G n)(x:ℝ)(J:Dart G n) : Prop where
    wave b a : ClimateJ R (Meld J x b a 0) x (trayF x) (wideM x)
    height b: ClimateJ R (boom (Meld J x) b 0) x (trayF x) (wideM x)
    core i: ClimateJ R (pluck (rim x) J i 0) x (trayF x) (wideM x)
    toE b a i : ClimateJ R (pluckD (rim x) J b a i 0) x (trayF x) (wideM x)
    mids b : ClimateJ R (stubJ (lush (YCore x J b))) x (trayF x) (2*thinM x)
lemma net(G:Gauge)(hG:G.Simple)(S:Stage)(k:ℕ)(hk:S.order≤k)(T:Collar G S.order):∃ C:ℝ,0≤ C∧∀ᶠ x:ℝ in atTop,∀ (n:Side)(Λ:ℝ)(R:Rep G n) (J:Dart G n)(A:ℝ)(h:Age S x Λ R), Cube.Wire R.p (high x) (h.rank.symm ▸ T) → 20*(high x+10)< n.val → Craft S x R J k A → C ≤ A → Wealth S R x J:=by
    obtain ⟨D,hD,H⟩:= shimmer G S k hk T
    refine ⟨max G.colorScale D,(G.colorScale_pos.le).trans (le_max_left ..),?_⟩;
    filter_upwards [wnt S (Cube.fee T) (Cube.fee_one T) S.order,Work.E01.radiusB_tendsto.eventually_ge_atTop 2] with x hx he n Λ R J A h hz hn Hf hh; have hx': D≤ A:= (le_max_right ..).trans hh; have hv: thinM x≤ wideM x:=wane _ (by norm_num)
    have hr : puff x+1+4≤ high x:= by unfold high; omega
    have hp(F:Peat G n)(j:ℕ)(hp:j≤high x)(hf: Splendor F (tower j) k (thinM x) A): ClimateJ R F x (trayF x) (wideM x):= (H x Λ n R h hz (by omega) _ F (Or.inl (Zn.post _ _ _ _ _ _ _ hx' (hf.up (sprout_mono _ hp) le_rfl) le_rfl))).plus (hx.1 _ hv) hv
    refine ⟨fun b a=>hp _ _ (by omega) ((Hf.peak b a).read 0),fun b=> hp _ _ hr ((Hf.bounce b).read 0),fun b=>hp _ _ (by omega) ((Hf.plum b).read 0),fun b a i=> hp _ _ (by omega) ((Hf.pearl b a i).read 0),fun b=>?_⟩
    have ht:=medal G hG S k A 0 ((le_max_left ..).trans hh) Unit n R J x Hf b; exact (H x Λ n R h hz (by omega) _ _ (Or.inr (mot k _ _ _ _ _ _ hx' (ht.plusR (dec_b ..|>.1)) le_rfl))).plus hx.2.1 le_rfl
end YM.Trace.Weir
