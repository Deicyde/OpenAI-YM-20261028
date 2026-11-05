import YM.Trace.FreeScalar
import YM.UVNext.FREE_STRESS_CERTIFICATE.Pressure
import YM.MergeProof.Emanate

/-!
An actual-field weak short-distance lemma on the same S and translation
normalization, *not* a rate estimate or a leading trace calculation. Uses
simultaneous Emanate comparison frames along one UV path and the rank-one
line of centered conserved tensors; no divergent-shell integral is taken here.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 80000
set_option maxRecDepth 12000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace
open Maxwell Labels Table Next.UVStress Org Climb Function Filter Set
open scoped Topology ContDiff BigOperators RealInnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book}
section
variable (F : Labels.Frames G)
open UVNext.FreeStress
lemma scalar_actual : total F = (4:ℝ) • scalarLabel F := by
  let U := Maxwell.Free.address F 4
  have hw (p q : Axis) (c : G.ColorIndex) : curlProbe (initialPlace p q) c = Maxwell.Free.omegaLeg c p q := by
    apply DFunLike.ext; intro x
    change Maxwell.Free.leg (YM.basis ∘ Fin.elim0) c p q x = _
    unfold Maxwell.Free.omegaLeg
    rw [show (basis ∘ (Fin.elim0 : Fin 0 → Axis))=(fun _ => 0) from Subsingleton.allEq ..]
  have he (p q a b) : U (flat F p q a b) = Maxwell.Free.phi p a q b := by
    change Maxwell.observable G 4 ((F.level 4).coords.symm ((F.level 4).coords _)) = _
    rw [LinearEquiv.symm_apply_apply]
    simp only [UVNext.FreeStress.ff,shell_bond,hw]
    rfl
  apply Maxwell.Free.address_inj F 4
  unfold total
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,scalar_address]
  dsimp [actionScalar,Free.sheetEnergy]; change (U _ : WickPol G)= _
  simp only [map_sum,he]; change _ = (4 : ℂ) • ((↑(1/(4:ℝ)):ℂ)) • (_ : WickPol G)
  rw [smul_smul]; push_cast; module

lemma torch_traceless (t : ℝ) : ∑ a, torch F t a a=0 := by
    change ∑ a, t • canonicalStress F a a = 0
    rw [← Finset.smul_sum]
    suffices z : (∑ a : Axis, canonicalStress F a a)=0 by rw [z,smul_zero]
    simp only [canonicalStress,if_true,Finset.sum_sub_distrib]; unfold panel total
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
    norm_num

abbrev sumTrace (D : S.Stress) := ∑ a : Axis, D a a
noncomputable def actAt (X : Scaling S) (k : ℕ) := X.U k 4 (scalarLabel C.book.grid)
end
end YM.Trace

namespace YM.Trace
open Maxwell Labels Table Next.UVStress Org Climb Function Filter Set
open scoped Topology ContDiff BigOperators RealInnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {Q : MaxwellData C}
variable {V : DiffPlan S} {I : IR (C:=C) S} {H : Org.UV C f S V Q I} {c : ℝ} {U : ∀ d, Spin.change S d} {Y : S.Stress}

lemma centeredLine (hY : Org.Tab S V Q I H c U Y) (hI : I.J≠0) (he : I.J∈KernelSpace H.basis.kernel.spin)
     (p : FreeDiv Q.T Q.hT Q.lit.hers) (X : Scaling S) (hX : Approaches (path X) (isoPanel X))
     (hS : Stable H.basis.kernel.spin Q.hT.spin V Q.T.W X) : ∃ a : ℝ, reCenter S Y=a • I.J := by
    let A := H.basis.kernel
    have h := enters A Y (sym_mem.mpr ⟨hY.locality.conserved.symmetric,hY.locality.conserved.real,
      fun k i j => ?_⟩)
    rotate_left
    · rw [← hY.locality.spots.signed]; exact hY.locality.spin k.ortho i j
    let j : KernelSpace A.spin := ⟨_,h⟩
    let i : KernelSpace A.spin := ⟨_,he⟩
    have hj : currentDiv V A.spin H.aligned j = 0 := by
      apply (linear_cons ..).mpr
      refine ⟨(sym_mem.mp (kernel_mem.mp j.property).1).1,(sym_mem.mp (kernel_mem.mp j.property).1).2.1,?_⟩
      intro b
      change ∑ a, V.deriv 4 a (centering S 4 _)=0
      have ht := V.unit_drop A.laws hY.locality.derivatives A.smooth 4
      simp only [value_center,map_sub,map_smul,ht,smul_zero,sub_zero,hY.locality.conserved.divergence]
    have hi : currentDiv V A.spin H.aligned i=0 := (linear_cons ..).mpr H.planet.tensor
    have hz := (differential_rank A Q.hT H.aligned Q.T Q.lit.hers p hY.locality.derivatives Q.lit.pales X hX hS).2
    let e : LinearMap.ker (currentDiv V A.spin H.aligned) := ⟨i,hi⟩
    have hm : e≠0 := fun h => hI (congr_arg (fun u => ((u : LinearMap.ker (currentDiv V A.spin H.aligned)).val).val) h)
    obtain ⟨b,hb⟩ := (finrank_eq_one_iff_of_nonzero' e hm).1 hz ⟨j,hj⟩
    exact ⟨b,(congr_arg (fun u => u.val.val) hb).symm⟩

lemma meterLimit (hY : Tab S V Q I H c U Y) (X : Scaling S) (hX : Approaches (path X) (isoPanel X))
     (hS : Stable H.basis.kernel.spin Q.hT.spin V Q.T.W X) (hp : X.meter I.J Q.T.J) :
     Tendsto X.xi atTop (𝓝 (|c|/|Q.T.κ|)) := by
    let A := H.basis.kernel
    let hVi := hY.locality.injection
    let hV := hY.locality.derivatives
    obtain ⟨D,N,m,R,hR,he⟩ := (Work.A05.answer A V hVi hV Q I.J 4 I.p I.Y H.planet).ask
    obtain ⟨E,n,k,B,hB,ht⟩ := (Work.A04.answer A V hVi hV Q I.J 4).ask
    obtain ⟨a,ha⟩ := focused_track A hV Q.hT Q.T Q.lit.pales X hX hS I.J hp (max N n) (max D E) (max m k) (max R B) (hR.trans (le_max_left ..))
    let g := afterScale X a
    obtain ⟨hw,-⟩ := he _ _ _ _ _ (le_max_left ..) (le_max_left ..) (le_max_left ..) (le_max_left ..) ha
    have hK := ht _ _ _ _ _ (le_max_right ..) (le_max_right ..) (le_max_right ..) (le_max_right ..) ha
    let F := leaves Q.T.W.deriv 4
    have hf : leaves (Q.T.κ • Q.T.W.deriv) 4 = Q.T.κ • F := rfl
    unfold Bid.ConLap at hw hK
    simp_rw [hY.Γ.sizes] at hw
    let g₀ i := g.r i • g.aisle i 4 (leaves V.deriv 4)
    have hq i : (g.r i/g.xi i) • g.aisle i 4 (c • leaves V.deriv 4) = (c / g.xi i) • g₀ i := by
        unfold g₀; rw [map_smul,smul_smul,smul_smul]; congr 1; ring
    change Tendsto (fun i => (g.r i / g.xi i) • g.aisle i 4 _) _ _ at hw
    simp_rw [hq] at hw; rw [hf] at hw
    have h₀ : ‖F‖≠0 := (@norm_pos_iff (Climb.Vector 4 (Bel C.book)) _ F |>.mpr Q.lit.born).ne'
    have hd := Filter.Tendsto.norm (E:=Climb.Vector 4 (Bel C.book)) hK
    change Tendsto (fun i=>‖g₀ i‖) atTop (𝓝 ‖F‖) at hd
    letI hwNS : NormSMulClass ℝ (Climb.Vector 4 (Bel C.book)) := @NormedSpace.toNormSMulClass ℝ (Climb.Vector 4 (Bel C.book)) _ _ _
    have hw' : Tendsto (fun i=>|c| / |g.xi i| * ‖g₀ i‖) atTop (𝓝 (|Q.T.κ| * ‖F‖)) := by simpa [norm_smul (α:=ℝ) (β:=Climb.Vector 4 (Bel C.book)),Real.norm_eq_abs] using Filter.Tendsto.norm (E:=Climb.Vector 4 (Bel C.book)) hw -- maybe simp
    have hξ : Tendsto (fun i => |c| / g.xi i) atTop (𝓝 |Q.T.κ|) := Tendsto.congr' ((hd.eventually_ne h₀).mono fun i hi => by
          change (|c| / |g.xi i|) * ‖g₀ i‖ / ‖g₀ i‖=|c|/g.xi i
          rw [mul_div_cancel_right₀ _ hi,abs_of_nonneg (g.sign i).le]) (by
        have hz := hw'.div hd h₀
        rw [mul_div_cancel_right₀ _ h₀] at hz
        exact hz)
    rw [← tendsto_add_atTop_iff_nat a]
    exact (tendsto_const_nhds (x:=|c|) |>.div hξ (abs_pos.mpr Q.T.hκ).ne').congr fun i=> by
       have hc : c≠0 := hY.Γ.positive
       change |c| / (|c| / g.xi i)=g.xi i
       rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ ((abs_pos.mpr hc).ne')]
end YM.Trace

namespace YM.Trace
open Maxwell Labels Table Next.UVStress Org Climb Function Filter Set
open scoped Topology ContDiff BigOperators RealInnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {Q : MaxwellData C}
variable {V : DiffPlan S} {I : IR (C:=C) S} {H : Org.UV C f S V Q I} {c : ℝ} {U : ∀ d, Spin.change S d} {Y : S.Stress}
private lemma center_map {M : Register G} {T : Table M} (u : T.Field 4 →ₗ[ℂ] S.Field 4) (h : u (T.unit 4) = S.unit 4) (A : S.Basic) (x : T.Field 4) :
     centering S 4 (u (centering T 4 x)) = centering S 4 (u x) := by
     rw [value_center x,map_sub,map_smul,map_sub,map_smul,h,const_out A,smul_zero,sub_zero]

local notation "F"=> C.book.grid

noncomputable def payload (X : Scaling S) (k : ℕ) (J : Stress S) := centering (Bel C.book) 4 ((X.U k 4).symm ((X.r k)^4 • sumTrace (reCenter S J)))
private lemma returns (J : Stress S) (A : S.Basic) (X : Scaling S) {k} (hu : X.U k 4 ((Bel C.book).unit 4)=S.unit 4) :
      centering S 4 (X.U k 4 (payload X k J)) = (X.r k)^4 • centering S 4 (sumTrace J) := by
      unfold payload
      -- push center then maps
      rw [show centering S 4 (X.U k 4 (centering (Bel C.book) 4 _)) = centering S 4 ((X.r k)^4 • sumTrace (reCenter S J)) from ?_]
      rotate_left
      · simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using @center_map G C S _ (Bel C.book) (X.U k 4).toLinearMap hu A ((X.U k 4).symm ((X.r k)^4 • sumTrace (reCenter S J)))
      change ((centering S 4).restrictScalars ℝ) ((X.r k)^4 • sumTrace (reCenter S J)) = _
      rw [(((centering S 4).restrictScalars ℝ).map_smul (X.r k^4) _)]
      change X.r k^4 • (centering S 4) (sumTrace (reCenter S J)) = _
      rw [show sumTrace (reCenter S J)=centering S 4 (sumTrace J) from (map_sum (centering S 4) (fun i => J i i) _).symm,
        value_center (sumTrace J),map_sub,map_smul, const_out A,smul_zero,sub_zero]
      nth_rewrite 1 [value_center]; rfl

open UVNext.FreeStress
lemma paint_sum (a b d : ℝ) : (∑ i : Axis,(UVNext.FreeStress.paintStress F a b d) i i) = (a+2*b) • UVNext.FreeStress.total F := by
   simp only [paintStress,Pi.add_apply,Pi.smul_apply,east,west,splitDiag,across,if_true,smul_zero,add_zero,Finset.sum_add_distrib,
      ← Finset.smul_sum]
   have h (i : Axis) : far F i = total F - (2:ℝ) • near F i := by rw [total_at F i]; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (2:ℝ)]; push_cast; abel
   rw [show ∑ x : Axis, near F x = total F by rfl]; simp_rw [h]
   rw [Finset.sum_sub_distrib,Finset.sum_const,← Nat.cast_smul_eq_nsmul ℝ, ← Finset.smul_sum,
       show ∑ x : Axis, near F x = total F by rfl]; norm_num; module

lemma money_ne_zero (h : G.Simple) : scalarLabel F ≠0 := by
    letI : Nontrivial G.Color := h.nontrivial_color
    have h₀ : 0 < G.lieDim := by rw [show G.lieDim=Module.finrank ℝ G.Color from G.colorIso.finrank_eq.symm]; exact Module.finrank_pos
    have hx : 0≠basis timeAxis := by intro hx; have h := basis_norm timeAxis; rw [← hx,norm_zero] at h; norm_num at h
    have he := reference_pair F hx
    have ht : ((3*(G.lieDim:ℝ)/Real.pi^4:ℝ)/‖0-basis timeAxis‖^8)>0 := by have := Real.pi_pos;simp; positivity
    have hi : (∑ i∈(∅ : Finset ℕ), (0:ℝ))=0 := by simp -- force predictable
    rintro hQ
    rw [hQ] at he
    -- useAt isilinear
    let W := Maxwell.Free.Model F
    have e0 : (W.classMoment W (n:=2) (fun _ => 4) (Maxwell.Free.pairPoints 0 (basis timeAxis))) 0=0 := MultilinearMap.map_coord_zero _ (0:Fin 2) rfl
    exact (Complex.ofReal_ne_zero.mpr ht.ne') (by simpa using (he.symm.trans e0))

lemma total_ne_zero (h : G.Simple) : UVNext.FreeStress.total F ≠ 0 := by rw [scalar_actual]; exact smul_ne_zero (by norm_num) (money_ne_zero h)

lemma payload_exact (hY : Tab S V Q I H c U Y) (X : Scaling S) (hS : Stable H.basis.kernel.spin Q.hT.spin V Q.T.W X) (hG : G.Simple) : ∀ᶠ k in atTop,
       ∃ a : ℝ, payload X k Y = a • UVNext.FreeStress.total F := by
   filter_upwards [vector_coherence H.basis.kernel Q.hT hS (d:=4), hS.units 4] with k hk hu
   let A := H.basis.kernel
   have h := enters A Y (sym_mem.mpr ⟨hY.locality.conserved.symmetric,hY.locality.conserved.real, fun k i j => ?_⟩)
   rotate_left
   · rw [← hY.locality.spots.signed]; exact hY.locality.spin ..
   let j : KernelSpace A.spin := ⟨_,h⟩
   let i : KernelSpace A.spin := X.r k ^4 • j
   let j' := sending A Q.hT (flips hk) i
   obtain ⟨a,b,d,hb⟩ := UVNext.FreeStress.exhaust F Q.hT.spin hG j'
   refine ⟨a+2*b, ?_⟩
   rw [show payload X k Y = (∑ t, j'.val t t) from ?_,hb]; exact paint_sum a b d (C:=C)
   change payload X k Y = ∑ t : Axis, centering (Bel C.book) 4 ((X.U k 4).symm ((X.r k)^4 • reCenter S Y t t))
   unfold payload
   rw [← map_sum,← map_sum,← Finset.smul_sum]

lemma rawPayload_tendsto (hY : Tab S V Q I H c U Y) (hI : I.J≠0) (he : I.J∈KernelSpace H.basis.kernel.spin)
     (p : FreeDiv Q.T Q.hT Q.lit.hers) (X : Scaling S) (hX : Approaches (path X) (isoPanel X))
     (hS : Stable H.basis.kernel.spin Q.hT.spin V Q.T.W X) (hT : Q.T.J = UVNext.FreeStress.torch F 1)
     (hQ : X.meter I.J Q.T.J) (_hG : G.Simple) : Tendsto (fun k => (X.U k 4).symm (X.r k^4 • sumTrace (reCenter S Y))) atTop (𝓝 0) := by
   obtain ⟨c',hc⟩ := centeredLine hY hI he p X hX hS
   have hg i (t : Axis) := hQ i t
   have hp := meterLimit hY X hX hS hQ
   have ht := tendsto_finsetSum Finset.univ (fun i _ => hp.smul (hg i i))
   -- want goal derivative of sum, no scaling leftover
   rw [hT,← Finset.smul_sum,torch_traceless] at ht
   simp only [smul_zero] at ht
   have ht' := (tendsto_const_nhds (x:=c')).smul ht
   simp only [smul_zero] at ht'
   have hb (k i) : c' • X.xi k • (X.U k 4).symm ((↑((X.xi k)⁻¹ * X.r k ^4):ℂ) • I.J i i) =
        (X.U k 4).symm ((X.r k)^4 • ((c' • I.J : S.Stress) i i)) := by
             let z := X.r k^4 • I.J i i
             have hZ (v : ℝ) (x : S.Field 4) : (X.U k 4).symm (v • x) = v • (X.U k 4).symm x :=
                 ((X.U k 4).symm.toLinearMap.restrictScalars ℝ).map_smul _ _
             rw [show ((c' • I.J : S.Stress) i i) = c' • I.J i i by rfl, smul_comm (X.r k^4) c',hZ,
                 Complex.coe_smul,mul_smul,hZ]
             exact congrArg (c' • ·) (show X.xi k • (X.xi k)⁻¹ • (X.U k 4).symm z = (X.U k 4).symm z from
             smul_inv_smul₀ (by linarith [X.sign k] : X.xi k ≠0) _)
   refine ht'.congr (by intro k; rw [Finset.smul_sum]; simp only [hb,hc,Finset.smul_sum,map_sum])
lemma exists_moneypath (hY : Tab S V Q I H c U Y) (hI : I.J≠0) (he : I.J∈KernelSpace H.basis.kernel.spin)
     (p : FreeDiv Q.T Q.hT Q.lit.hers) (X : Scaling S) (hX : Approaches (path X) (isoPanel X))
     (hS : Stable H.basis.kernel.spin Q.hT.spin V Q.T.W X) (hT : Q.T.J = UVNext.FreeStress.torch F 1)
     (hQ : X.meter I.J Q.T.J) (hG : G.Simple) : ∃ d : ℕ → ℝ, Tendsto d atTop (𝓝 0) ∧
        ∀ᶠ k in atTop, X.r k^4 • centering S 4 (sumTrace Y)=(4*d k) • centering S 4 (actAt X k) := by
   classical
   let d (k : ℕ) := if h : ∃ d : ℝ,payload X k Y = d • UVNext.FreeStress.total F then h.choose else 0
   have hl : ∀ᶠ k in atTop, payload X k Y=d k • UVNext.FreeStress.total F := by
      filter_upwards [payload_exact hY X hS hG] with k hk; unfold d; rw [dif_pos hk]; exact hk.choose_spec
   have hx : Tendsto (payload X · Y) atTop (𝓝 0) := by
      simpa only [payload,map_zero] using! ((centering (Bel C.book) 4).continuous_of_finiteDimensional.continuousAt (x:=0)).tendsto.comp
       (rawPayload_tendsto hY hI he p X hX hS hT hQ hG)
   refine ⟨d,?_,?_⟩
   · have hz := (total_ne_zero (C:=C) hG)
     have hf := ((hx.congr' hl).norm.div_const ‖UVNext.FreeStress.total F‖)
     have hw : Tendsto (fun k=> ‖d k‖ / 1) atTop (𝓝 0) := by
         rw [norm_zero,zero_div] at hf; convert! hf using 1
         funext k; simp [norm_smul (α:=ℝ),mul_div_cancel_right₀ _ ((@norm_pos_iff ((Bel C.book).Field 4) _ _).mpr hz).ne']
     refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hw.neg) (by simpa using hw)
         (show ∀ i, -(‖d i‖/1) ≤ d i by intro i; simp only [div_one,Real.norm_eq_abs]; exact neg_abs_le _) (fun i=>by exact le_abs_self _)
   filter_upwards [hl, hS.units 4] with k hl hu
   rw [← returns Y H.basis.kernel.laws X hu,hl,scalar_actual]
   let K4 := (centering S 4).restrictScalars ℝ
   let W4 := ((X.U k 4).toLinearMap.restrictScalars ℝ)
   change K4 (W4 _) =  (4* d k) • K4 _
   simp_rw [W4.map_smul,K4.map_smul,smul_smul]
   rw [mul_comm]; rfl

end YM.Trace
