import YM.RG08.Curl.Sloop
/-! # whole-loop completions relative to gauge invariant reference
-/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Virtue
open Filter MeasureTheory Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free Conductor UVExt.Paths Push.AbsoluteSums Staffer
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {A B C σ η : ℝ} {r s d n : ℕ}
variable {F : Atlas G} {i : G.ColorIndex}

-- admiss
structure Fleet (G : Gauge) (i:G.ColorIndex)(F : Panel G)(d:ℕ) : Prop where
    tune : ∀ j≤d+2,Tunable (F j)
    model m : ∃ f:Link G m→ℝ, Pointwise f ∧ ∀ j ≤ d+2, Tensor.coeff f j 0=recital (F j) m
    nullF : F 0=0
    cur : probeK i (F 2)=0
-- Finite series frame: use true unmasked invariant sums.
structure Artefact (F:Panel G)(d:ℕ)(σ A:ℝ)(T : Flotilla G): Prop where
    lanes : exalts T (embark 0 (d+1)) σ A
    march : Flute G (T 0)
    value m j(h:j≤ d+2) : Tensor.coeff (shores T (embark 0 (d+1)) m) j 0=recital (F j) m
lemma portside {T : Flotilla G}{k:Finset ℕ}(h : exalts T k σ A)(he:0<σ): ∀ m,Pointwise (shores T k m) := by
  intro m
  induction k using Finset.induction_on with
  | empty=> unfold shores; rw [sum_empty]; simpa using! Pointwise.coin (F:=WilsonQ G m) Wilson_witness 0
  | insert i s hi ih=> rw [shores,sum_insert hi]; have hp:= (h i (mem_insert_self ..)).pathways; exact (stain_ink _ he hp.1 hp.2).add (ih fun i hi=> h i (mem_insert_of_mem hi))

-- relative packet supplies
lemma boat (hG:G.Simple) (ν:G.ColorIndex) (d:ℕ)(hp:0<σ):∃ η C:ℝ,0<η∧ η≤σ∧ 0≤C ∧ ∀ A (F:Panel G), Fleet G ν F d → (∀ i≤d,Glow (F (i+2)) σ A) → ∃ T,Artefact F d η (A*C) T := by
  obtain ⟨w,J,hW,h,hJ,H⟩:= near hG ν hp
  obtain ⟨v,Q,hv,hq,hQ,hr⟩:= foilPaid G hW 1 (r:=1) rfl (1+d)
  obtain ⟨η,C,ht,hm,hC,hF⟩:= pilots G d 1 (by decide) hv
  refine ⟨η,J+(1+J*Q)*C,ht,(hm.trans hq).trans h,by positivity,fun A F Hf hE=>?_⟩
  choose f he Hm using Hf.model
  have hi m: Rays 2 (f m):= by
     apply (rays_jet (he m).analytic _).2
     have hx : Tensor.coeff (f m) 0 0=0:= (Hm m 0 (by omega)).trans (by rw [Hf.nullF,recital_zero])
     intro j hj; interval_cases j
     · simpa [Tensor.coeff] using hx
     have hk:= first_nil hG (he m); simpa [Tensor.coeff] using hk
  have hf:= hE 0 (Nat.zero_le _); have hz := hf.nonneg
  obtain ⟨X,hX,hD,hs⟩:=H f (F 2) A hf (Hf.tune _ (by omega)) (fun m=>⟨he m,hi m,Hm m _ (by omega)⟩) Hf.cur
  have hI m := (stain_ink _ hW hX.pathways.1 hX.pathways.2 (m:=m))
  let U m := f m-turnSeries (m:=m) (Stationary.issue X)
  have hh m : Pointwise (U m):= (he m).sub (hI m)
  have hV : Funds f 1 d σ A := by
     intro j hj
     have hp' : j≤d:= by simp only [embark,mem_Ico] at hj; omega
     let V:=F (j+2)
     exact ⟨gallery V,fun i j=>gallery_funds (hE _ hp') hp i j,fun m=> gallery_marks (Hf.tune _ (by omega)) (Hm m _ (by omega))⟩
  have hU: Funds U 1 d v (A*(1+J*Q)) := lightening (r:=0) hW X A (A*J) _ _ _ _ hz hX f 1 d hV he (fun i hi=> hr X _ (mul_nonneg hz hJ) hX (i+1) (by simp only [embark,mem_Ico] at hi; omega)) (hq.trans h) hv (le_of_eq (by ring)) -- toMar no
  obtain ⟨T,hT,hα⟩:= hF U _ (by positivity) (fun m=> ⟨hh m,hs m⟩) hU
  let P:=Function.update T 0 X
  have hL : exalts P (embark 0 (d+1)) η (A*(J+(1+J*Q)*C)) := by
    intro i hi
    by_cases hx:i=0; · rw [hx]; unfold P; rw [update_self]; exact hX.mono (by nlinarith [mul_nonneg hz hC,mul_nonneg (mul_nonneg hz hJ) hQ,mul_nonneg (mul_nonneg (mul_nonneg hz hJ) hQ) hC]) (hm.trans hq)
    unfold P; rw [update_of_ne hx]; exact (hT i (by simp only [embark,mem_Ico] at *; omega)).mono (by nlinarith [mul_nonneg hz hJ]) le_rfl
  refine ⟨P,hL,by unfold P; rw [update_self]; exact hD,fun m j hj=>?_⟩
  let W:=shores P (embark 0 (d+1)) m
  have hU : Rays (d+2+1) (f m - W):= by
     unfold W P; rw [splice_head]
     convert (hα m) using 1; omega; unfold U; abel
  have hu:= portside hL ht m
  have hk:= (rays_jet ((he m).sub hu).analytic _).mp hU j (by omega)
  rw [iteratedFDeriv_sub_apply (he m).analytic.contDiffAt hu.analytic.contDiffAt] at hk
  rw [← Hm m _ hj]; exact congr_arg (fun M=> ((j.factorial:ℝ)⁻¹) • M) (sub_eq_zero.mp hk).symm
end YM.RG08.Virtue
