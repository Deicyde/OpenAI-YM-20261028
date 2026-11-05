import YM.Planned.PRIMARY_INTEGRAL_295.Cabins

/-!
# payment for COB b along actual Probe paths

Use `Hol.testLinks` with the canonical alignment paid by Archive (symmetric Motion
elsewhere). Radius cutoff always on torus. Buffer agreement at every
required derivative point in Cabins for forecast identity. No pretending
polynomial extension to actual global schedule, cost polynomial post at
normalization and Lxe. Fount receives these proofs later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Flutes
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place
open Precision Exterior Tree Streets Porous Carrier Bloch Next.Free Progress.StationaryScenes  Bazaars Launch Shapes
open WardBin WardBin.Lies WardBin.Wheels Racks Dials Ramble Cabins PPX Laurent
open Push.Local (Probe)
open scoped Topology ContDiff BigOperators NNReal Classical Matrix.Norms.Frobenius
variable {G : Gauge} {T : Finset Cover} {k l d : ℕ} {t ξ s M δ u : ℝ} {F : Labels.Frame G d} {c f : Side}
variable {S : StepData c f}

section
variable (Z:Probe G d) (H:Hol G)
def fare (c:Side) (θ:ℝ):ℝ→Config G c := H.testLinks d 0 (θ • Z.1)
def lode (c:Side) (θ t:ℝ) (r:ℕ):ℝ→Dir G c := patched t (1:Site c→G.El) r (fare Z H c θ)

lemma fare_zero (θ:ℝ):fare Z H c θ 0=1:=by funext i; simp only [fare,Hol.testLinks,H.flat]; rfl




lemma stems (x:Cover):x∈box (size x):=by
   rw [box_test]; constructor <;> intro i <;> have hp : (x i).natAbs ≤ size x:= Finset.single_le_sum (f:=fun i=>(x i).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i) <;> omega
lemma cards (x:Cover) (r:ℕ) (h:x∈box r):size x ≤ 4*r:=by
   obtain ⟨h1,h2⟩:=box_test.mp h
   have hp i : (x i).natAbs≤r:= by have hl:=h1 i; have hu:=h2 i; omega
   simpa [size,Axis] using Finset.sum_le_sum (s:=Finset.univ) (g:=fun _=>r) (fun i _=>hp i)
lemma nose (c:Side) (θ t:ℝ) (r:ℕ) (e:Edge (Site c)): (fun y=>lode Z H c θ t r y (Work.E03.poleEquiv c e))=
    if separation 0 e.1 ≤ r then script Z t θ (lift e.1) e.2 else 0 := by
    ext1 y; unfold lode; rw [symbolic]; unfold room; split<;> rename_i h
    · rw [script_truth Z H (lift e.1,e.2) t θ]; simp only [Lattice.gauge,Pi.one_apply,one_mul,inv_one,mul_one,fare,Hol.testLinks,sub_zero]
    rfl
lemma cost_curve {θ t π:ℝ} (hb:PPX.Blend π t θ) (r χ:ℕ) (hχ:χ≤r) (hc:2*r<c.val):
    FacePrice Z H (lode Z H c θ t r) χ t θ:=by
   intro x hx
   have he:= peel hc x (within (hx.trans hχ) (stems x))
   refine ⟨he,fun i=>?_⟩
   refine Eventually.of_forall fun y=> ?_
   change t • (fun y=>lode Z H c θ t r y (Work.E03.poleEquiv c (wrap c x,i))) y=_
   rw [nose, if_pos ((spans x c).trans (hx.trans hχ)),script_truth Z H (lift (wrap c x),i) t θ,smul_inv_smul₀ hb.fine.ne']
   simp only [Hol.testLinks,sub_zero]

-- polynomial post, constants here can be chosen ahead independent of c.
lemma royalty (π : ℝ) (hp:1≤π):∃ N:ℝ,1≤N∧∀ (c:Side) (r:ℕ) (θ t:ℝ), PPX.Blend π t θ→
     let v:=lode Z H c θ t r
     ContDiffAt ℝ (Z.2.val:WithTop ℕ∞) v 0 ∧ Envelope 0 Z.2.val v (N*(1+4*(r:ℝ))^(d*Z.2.val)) := by
   choose C hc hC using gathered Z π hp
   let k:=Z.2.val; let u:=Finset.range (k+1); let N:=1+∑ n∈u,C n
   have hN : 1≤N := le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> hc i)
   have hh n (hn:n≤k): C n≤N:= (Finset.single_le_sum (fun i _=> hc i) (show n∈u from Finset.mem_range.mpr (Nat.lt_succ_of_le hn))).trans
       (le_add_of_nonneg_left zero_le_one)
   refine ⟨N,hN,fun c r θ t hb=>?_⟩; intro v
   let b(e:Edge (Site c)):=ContinuousLinearMap.proj (φ:=fun _ : Body 1 c=>G.Color) (R:=ℝ) (Work.E03.poleEquiv c e)
   have ht(e:Edge (Site c)):b e ∘ v= if separation 0 e.1 ≤r then script Z t θ (lift e.1) e.2 else 0 := nose Z H c θ t r e
   have hf : ContDiffAt ℝ (k:WithTop ℕ∞) v 0 := contDiffAt_pi.mpr fun i=> by
      obtain ⟨i,rfl⟩:= (Work.E03.poleEquiv c).surjective i; change ContDiffAt ℝ _ (b i∘ v) _
      rw [ht]; split
      · exact (script_smooth Z ..).of_le le_top
      exact contDiffAt_const
   let M:= N*(1+4*(r:ℝ))^(d*Z.2.val); have hM :0≤M := by unfold M; positivity
   refine ⟨hf,hM,fun n hn=>?_⟩
   apply ContinuousMultilinearMap.opNorm_le_bound hM; intro X
   apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (by positivity))).2; intro i
   obtain ⟨i,rfl⟩:= (Work.E03.poleEquiv c).surjective i
   change ‖b i (iteratedFDeriv ℝ n v 0 X)‖ ≤ _
   rw [show b i (iteratedFDeriv ℝ n v 0 X)=iteratedFDeriv ℝ n (b i ∘ v) 0 X from by rw [(b i).iteratedFDeriv_comp_left hf (Nat.cast_le.mpr hn)]; rfl,ht]
   split<;> rename_i h
   · let q:=lift i.1; let V:=script Z t θ q i.2
     have hC := (hC n θ t hb).1
     apply ((iteratedFDeriv ℝ n V 0).le_opNorm _).trans; apply mul_le_mul_of_nonneg_right _ (by positivity)
     rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]; apply (hC.2 q i.2).trans; change C n*_≤M
     have hd:= cards q r (by simpa [q] using Work.E08.lift_mem_box h)
     have hk : liftCost (d*n) q ≤ (1+4*(r:ℝ))^(d*Z.2.val):= by
       apply (pow_le_pow_left₀ (show 0≤1+(size q:ℝ) by positivity) (add_le_add_right (show (size q:ℝ) ≤4*(r:ℝ) by exact_mod_cast hd) _) (d*n)).trans
       apply pow_le_pow_right₀ (by simp) (Nat.mul_le_mul_left d hn)
     exact mul_le_mul (hh n hn) hk (liftCost_pos ..) (by positivity)
   simp only [iteratedFDeriv_zero,Pi.zero_apply]; simpa only [zero_apply,norm_zero] using mul_nonneg hM (show 0≤∏ i,‖X i‖ by positivity)
end
end YM.Planned.PrimaryIntegral295.Flutes
