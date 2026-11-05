import YM.RG05Readout.Offsets.Predict
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Pieces
/-!
# Registered stencil at offset, on true torus
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Offsets
open Function Filter Set Lattice Wilson MeasureTheory Pressure RG Precision Labels Source Source.Drops
open Push.Local Planned.PrimaryIntegral295 PPX Flutes Place Bazaars Exterior Streets
open WardBin.Lies Cabins Bid
open Tree Next.Free Matrix Bloch Next Next.Foundations
open PhysicalNext.Repeat PhysicalNext.JointLoad Heir Cub Trace.Physical.GermShift
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S: StepData c f}{T: Pressure.Tube G S} {d n j t : ℕ}
variable {F:Labels.Frame G d}

/-- Adapt `Cub.terra` to simultaneous halo stencil with the offset still alive. -/
lemma torus_stencil (M:SectionData F)(w y:ℝ)(hw:0<w)(x:ℝ)(A:Hol G)(p:Probe G d)(i:F.Index)(a:Cover):
    Cub.ocean T (Push.Local.presented M (wrap f a) w (Place.copy F i)) x ∘ Flutes.fare p A c y =
      atColumn M i a w ∘ ((Bazaars.earth (translatedSupport a M.stencil) S T.R.A0) ∘ Flutes.lode p A c y w (reach x)):= by
  have hl : F.scaled w⁻¹ (Place.copy F i)= (((w^(F.grades i).2)⁻¹:ℝ):ℂ) • Place.copy F i:=by
    ext1 j; by_cases h:j=i <;> simp [h,Place.copy]
  have hv (V:Config G f): Push.Local.presented M (wrap f a) w (copy F i) V=
      (w^(F.grades i).2)⁻¹ • M.places (copy F i) (wrap f a) V:=by
    unfold Push.Local.presented; change M.places _ _ _ = _; rw [hl]
    unfold SectionData.places SectionData.evaluate; rw [map_smul,map_smul]; exact (Complex.real_smul ..).symm
  funext z
  let U:=translatedSupport a M.stencil
  let D:=Flutes.lode p A c y w (reach x) z
  let X:= Streets.tapes S T.R.A0 D
  have hz:S.ratio.parent (0:Site f)=0:=by let q:=S.ratio; change q.parent 0=0; rw [← q.root.map_zero]; exact q.embed_parent _
  change Push.Local.presented _ _ _ _ _ = (w^(F.grades i).2)⁻¹ • there M i a (w • Bazaars.earth U S T.R.A0 D)
  rw [hv]; refine congr_arg ((w^(F.grades i).2)⁻¹ • ·) ?_
  simp only [hz,Cub.stole _ _ hw z,map_smul,Cub.walked]
  let Y := Bazaars.earth U S T.R.A0 D
  rw [there,Function.comp_apply]
  change M.evaluate (copy F i) (expandAt (wrap f a) (increment 1 (w • X)))= M.evaluate _ _
  apply M.cylinder_local; intro e hi hj
  unfold pore; split
  · next hh =>
    change increment (1:Config G f) (w • X) (wrap f e.1+ wrap f a,e.2) = G.lieExp (w • X (wrap f (e.1+a),_))
    unfold increment; simp; rfl
  next hh => exact (hh ⟨hi,hj⟩).elim

lemma there_smooth (S:SectionData F) (i:F.Index)(a:Cover) : ContDiff ℝ ω (there S i a) :=
    (column_smooth S i).comp ((clip G (a:=a) (T:=translatedSupport a S.stencil) (S:=S.stencil) Finset.subset_union_right).contDiff)
set_option maxHeartbeats 400000 in
lemma there_cost (M:SectionData F) (i:F.Index) (a:Cover)(h:Bid.pop M) (k:ℕ) :
    ∃ x : ℝ, Tones.Width (there M i a) k (F.grades i).2 0 x := by
  haveI:= FiniteDimensional.proper ℝ (Dev (translatedSupport a M.stencil) G)
  refine Tones.on_body (there_smooth M i a) (fun j hj=> ?_) k _
  unfold there; rw [jets_linear _ (Place.column_smooth M i |>.contDiffAt.of_le (m:=(j:WithTop ℕ∞)) le_top),Place.radials_vanish M h i _ hj]; rfl

-- Keep the profile charges explicit (private geo helper).
lemma arc_log (t N:ℝ)(ht:0<t)(hh:1≤N)(k:ℕ): Tendsto (fun x:ℝ=> (1+N*(1+4*(Heir.reach x:ℝ))^k)*Real.exp (-t* Heir.reach x)) atTop (𝓝 0):=by
  let r (x:ℝ):ℝ:= Heir.reach x; have ha(x:ℝ):1≤r x:=by unfold r Heir.reach; exact_mod_cast (by omega:1≤45*(1+radiusB x))
  have hR:Tendsto r atTop atTop:= tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (g:=Heir.reach) (fun x=>by unfold Heir.reach; omega) Work.E01.radiusB_tendsto)
  have hp:= (((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp (hR.const_mul_atTop ht)).div_const (t^k)).const_mul ((1+N*(5^k:ℝ))); rw [zero_div,mul_zero] at hp
  refine squeeze_zero (fun x=>by positivity) (fun x => ?_) hp
  have h:= ha x
  change _ ≤ _ *((t*r x)^k* Real.exp (-(t*r x))/t^k)
  rw [mul_pow,mul_assoc,mul_div_cancel_left₀ _ (pow_ne_zero _ ht.ne')]
  rw [← mul_assoc, neg_mul]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hq:1+(4*r x) ≤5*r x:=by linarith
  rw [add_mul,one_mul,mul_assoc,← mul_pow]; exact add_le_add (one_le_pow₀ h) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by change 0≤1+4*r x; positivity) hq _) (zero_le_one.trans hh))

open Carrier Postcards
variable (p:Probe G d)(M:SectionData F)(A:Hol G) (h:M.Sound A) (hP:Bid.pop M)
include h hP
set_option maxHeartbeats 800000 in
/-- Starlight at retained offset a. At the same-weight and lower field probes,
    one may indeed use the same heading, within the post-block delay. -/
lemma retained {k:ℝ}(hk:0<k)(hj:4≤ j)(ht:4≤ t)(hd:d≤j)(i:F.Index)(hi:p.2.val≤ (F.grades i).1)
    (L:Side)(b:Cover){ε:ℝ}(he:0<ε):∀ᶠ x:ℝ in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(P:Flight j t), S.ratio.count=P.L→P.L=L→ HEq T.R.A0 (linesOf P k)→
    ∀ w y,∀ hB:Blend 2 w y, 2*Heir.reach x<c.val →
       let u:=ocean T (presented M (wrap f b) w (Place.copy F i)) x; let V := A.testLinks d 0 (y • p.1)
       let z:= Seal.donne M h hk ht hP P hd hB; ‖((L.val:ℝ)^d) • iteratedDeriv p.2.val (u ∘ (V:ℝ→ Config G c)) 0 - runProbe F p (z.leads L (Place.copy F i))‖ ≤ ε:=by
  let n:=p.2.val
  let U:= translatedSupport b M.stencil
  obtain ⟨s,D,hs,hD,H⟩:=Carrier.priced k hk hj ht
  obtain ⟨C,hC,hF⟩:=there_cost M i b hP (n+1)
  obtain ⟨z,hz,hZ⟩:=Ramble.billFor U p A 2 s D one_le_two hs hD.le
  obtain ⟨K,hK,hV⟩:= Flutes.royalty p A _ one_le_two
  choose! E h₁ h₂ using fun r=> Postcards.replicate U p 2 k one_le_two hk hj ht r
  let a:= ∑ n∈ Finset.range (p.2.val+1), E n; let Q':=(F.grades i).2
  have ha:0 ≤ a:= Finset.sum_nonneg fun i hi=> h₁ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  let v' := Oval.league n Q' a C
  let e(x:ℝ) := K*(1+4*(Heir.reach x:ℝ))^(d*n)
  let F0 (x:ℝ) := z*(1+e x)*Real.exp (-(s/2)*(Heir.reach x:ℝ))
  let v := (L.val:ℝ)^d
  have he' : Tendsto F0 atTop (𝓝 0):=by
    have h:= (arc_log _ _ (half_pos hs) hK (d*n)).const_mul z; rw [mul_zero] at h; exact h.congr (fun _=> (mul_assoc ..).symm)
  have hv0 := ((((tendsto_const_nhds (x:=v')).mul (((tendsto_const_nhds (x:=(1:ℝ))).add he').pow (Q'+n))).mul he').const_mul v); rw [mul_zero,mul_zero] at hv0
  filter_upwards [hv0.eventually (ge_mem_nhds he)] with x hx c f S T P hPs hQ hr w y hB hl
  intro u V Z
  have hh: Postcards.forecast U p (linesOf P k) y w = Postcards.forecast U p T.R.A0 y w:=by
    have he (i:Side)(X:Lines i)(hf:i=P.L) (h:HEq X (linesOf P k)): Postcards.forecast U p X y w= Postcards.forecast U p (linesOf P k) y w:=by subst i; rw [eq_of_heq h]
    exact (he _ _ hPs hr).symm
  let N':= Postcards.forecast U p (linesOf P k) y w
  have hf:N' 0=0:=Postcards.forecast_zero ..
  have hδ:= (Postcards.forecast_truth U p (linesOf P k) y w (Carrier.stored P k hk ht)).contDiffAt (x:=0)
  have hw: T.R.A0.strip s D:=by
    have h {v:Side}(u:Lines v)(hf:v=P.L)(h:HEq u (linesOf P k)): u.strip s D:=by
      subst v; rw [eq_of_heq h]; have he: (linesOf P k).strip s (D/P.L.val):=by simpa [advanceC] using H P [] (by simp)
      exact Work.F08.strip_mono he le_rfl (div_le_self hD.le (Nat.one_le_cast.mpr P.L.property))
    exact h _ hPs hr
  let e' := Flutes.lode p A c y w (Heir.reach x)
  let f₁ := (earth U S T.R.A0 ∘ e')
  have hκ : e' 0=0:=by
    unfold e' Flutes.lode Cabins.patched; ext1 i; unfold Cabins.room; split; · simp [Flutes.fare_zero,Lattice.gauge]
    exact rfl
  obtain ⟨hw',hψ⟩:= hV c (Heir.reach x) _ _ hB
  have hW: Oval.Fuzz 0 p.2.val f₁ N' (F0 x):=by
    unfold N'; rw [hh]; exact hZ c f S _ _ _ _ (e x) _ hB hw (Flutes.cost_curve p A hB _ _ le_rfl hl) hw' hψ
  have he:Oval.Envelope 0 n N' a:= ⟨ha,fun k' hn=> (h₂ k' hn P _ _ hB).trans
    (Finset.single_le_sum (fun i hi=>h₁ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))⟩
  let g (f:ℝ→Place.Dev U G):=atColumn M i b w ∘ f
  have hT:ContDiffAt ℝ (p.2.val:WithTop ℕ∞) f₁ 0:=(earth U S _).contDiff.contDiffAt.comp _ hw'
  have hp:=Oval.sticker (hδ.of_le le_top) hT hW he (there_smooth M i b)
    (show w∈Ioc (0:ℝ) 1 from ⟨hB.fine,hB.fits⟩) (show Tones.Width (there M i b) (n+1) Q' 0 C from ⟨hC,hF⟩)
    (by change ‖w • N' 0‖ ≤ 0; simp [hf]) (by simp [f₁,hκ])
  have hY: u ∘ V = g f₁:= torus_stencil M _ _ hB.fine x A p i b
  rw [hY, ← hQ]
  rw [show runProbe F p (Z.leads P.L _) = _ from Postcards.measured M h _ P k (2:ℝ) y w hk ht hd hB p i,
    ← predicts P M hk ht hd h i p hi b y w]
  rw [← smul_sub,norm_smul,Real.norm_of_nonneg (by positivity)]
  let I:= iteratedFDeriv ℝ n (g f₁) 0 - iteratedFDeriv ℝ n (g N') 0; let y':Fin n→ℝ:= fun _=>1
  have hI:‖I y'‖≤ v'*(1+F0 x)^(Q'+n)*F0 x:=by
    simpa only [y',v',n,Finset.prod_const_one,mul_one,norm_one] using ((I.le_opNorm y').trans (mul_le_mul_of_nonneg_right (hp.2.2.2 n le_rfl) (show 0≤∏ i : Fin n,‖(1:ℝ)‖ from Finset.prod_nonneg fun _ _=> norm_nonneg _)))
  change (P.L.val:ℝ)^d * ‖I y'‖ ≤ ε; rw [hQ]; exact (mul_le_mul_of_nonneg_left hI (by positivity)).trans hx
end YM.RG05Readout.Offsets
