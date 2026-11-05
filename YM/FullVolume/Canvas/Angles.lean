import YM.FullVolume.Canvas.Vigil
import YM.Next.STATIONARY.Loops.Curvature
/-! Universal index weighted paths in H.See PS nails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Shade
open Filter Set Function lp Lattice Laurent Bloch Exterior RG Precision Wilson Tralis
open scoped Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius NNReal ENNReal
variable {G:Gauge}{t:ℕ}[NeZero t]
abbrev InkSpot (G:Gauge)(t:ℕ):= ℕ × Ink G (t+1)
abbrev Cameo (G:Gauge)(t:ℕ):= Lights (InkSpot G t)
def letter (i:ℕ): Fin (t+1)→Slot:= fun j=> walkSlot (plaqEquiv.symm ((carrierPath t i).1 j)) ((Fin.cons (α:=fun _: Fin (t+1)=> Cover) (0:Cover) (fun k a=> (carrierPath t i).2 (k,a))) j)
lemma story (P:Skin G t)(i:ℕ): (issue P i).leg= letter i:=rfl
def stretch (t:ℕ)[NeZero t](i:ℕ):ℕ:= size (carrierPath t i).2+4*(t+1)
lemma pervade (A:ℕ→Atom G (t+1))(h:∀ i,(A i).leg=letter i)(i): (A i).length=stretch t i :=(show _ = (issue (0:Skin G t) i).length by unfold Atom.length; simp_rw [h,story (t:=t)]).trans (artery_length ..)
def chants (t:ℕ)[NeZero t] (σ:ℝ)(i:ℕ):=Real.exp (σ* stretch t i)
lemma silts (t:ℕ)[NeZero t]{σ:ℝ}(h:0<σ): Summable (chants t (-σ)):=by
    let f(x:Shift (Keys t)):= Real.exp (-σ*size x); have he: Summable f := (Width.compactPay (α:=Keys t) σ h).2.1
    let K:ℝ:= Real.exp (-σ*((4*(t+1):ℕ):ℝ)); have H: Summable (fun x:CurRun (t+1) × Shift (Keys t)=> f x.2*K) :=by
        exact (budget_prod_finite (f:=fun x:CurRun (t+1) × Shift (Keys t)=> f x.2*K) (A:=fun _=>∑' i,f i*K) (fun x=> ⟨fun i=> by unfold f K; positivity, he.mul_right K,le_rfl⟩)).2.1
    exact ((carrierPath t).summable_iff.mpr H).congr (fun i=> by unfold f K comp chants stretch; push_cast; ring_nf; rw [←Real.exp_add]; congr 1; ring)
variable (σ:ℝ)
def ringT (C:Cameo G t)(p:ℕ): Atom G (t+1):=⟨letter p,fun k=> C (p,k)/chants t σ p⟩
lemma weight (C:Cameo G t)(p) : (ringT σ C p).length=stretch t p:= pervade _ (fun _=>rfl) _
lemma feel (C:Cameo G t)(p:ℕ)(w:ℝ) : (ringT σ C p|>.budget w) = ∑ k : Ink G (t+1), chants t (w-σ) p*‖C (p,k)‖:=by
   unfold Atom.budget Atom.magnitude; rw [weight]; simp only [ringT,Finset.sum_mul,abs_div]
   have h : Real.exp (w* stretch t p)/chants t σ p=chants t (w-σ) p:=by unfold chants; rw [←Real.exp_sub]; congr 1; ring
   apply Finset.sum_congr rfl; intro x _; rw [← h, Real.norm_eq_abs]; rw [abs_of_pos (show 0<chants t σ p from Real.exp_pos _)]; ring
-- K.Route
noncomputable def credits (G:Gauge)(t:ℕ)[NeZero t](σ:ℝ):= (Fintype.card (Ink G (t+1)):ℝ)*(∑' i,chants t (-σ) i)
lemma waved (G:Gauge)(w:ℝ):0≤credits G t w:=by unfold credits; exact mul_nonneg (by positivity) (tsum_nonneg (fun _=>(Real.exp_pos _).le))
lemma radius (C:Cameo G t){δ:ℝ}(h:δ<σ)(b:ℝ)(hb:‖C‖≤ b) : SumBudget (fun i=> (ringT σ C i).budget δ) (credits G t (σ-δ)*b):=by
    let B(i:ℕ):=(Fintype.card (Ink G (t+1)):ℝ) * chants t (δ-σ) i * b
    have hX: Summable (chants t (δ-σ)) := by rw [← neg_sub σ δ]; exact silts t (sub_pos.mpr h)
    apply Work.F08.budget_minor (g:=B) -- #check
    · refine ⟨fun i=>mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) ((norm_nonneg _).trans hb), (hX.mul_left _).mul_right _,?_⟩
      unfold B credits; simp [tsum_mul_left,tsum_mul_right]
    · intro i; simp only [feel]; exact Finset.sum_nonneg fun j _=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    intro i; rw [feel]; calc
     _ ≤ ∑ _ : Ink G (t+1), chants t (δ-σ) i*b:=Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ((lp.norm_apply_le_norm (by norm_num) C _).trans hb) (Real.exp_pos _).le
     _ = _ :=by simp [B,mul_assoc]
lemma erect (V:ℕ→Atom G (t+1))(h:∀ i,(V i).leg=letter i){b:ℝ}(hp: SumBudget (fun i=>(V i).budget σ) b): ∃ g:Cameo G t, ringT σ g=V ∧ ‖g‖≤b:=by
    let C (j:InkSpot G t):= chants t σ j.1 * (V j.1).coeff j.2
    have he i : (V i|>.budget σ)=∑ k:Ink G (t+1), ‖C (i,k)‖:=by
        unfold Atom.budget Atom.magnitude; rw [pervade _ h,Finset.sum_mul]; simp only [C, norm_mul,Real.norm_eq_abs]; apply Finset.sum_congr rfl; intro k _; rw [abs_of_pos (show 0 < chants t σ i from Real.exp_pos _)]; exact mul_comm ..
    have hB(S: Finset (InkSpot G t)): (∑ i∈ S, ‖C i‖)≤ b:=by
        classical
        let U:= S.image Prod.fst
        calc
         _ ≤ ∑ i∈ U ×ˢ Finset.univ, ‖C i‖ := Finset.sum_le_sum_of_subset_of_nonneg (fun x hx=> Finset.mem_product.mpr ⟨ Finset.mem_image_of_mem _ hx,Finset.mem_univ _⟩) (fun i _ _=> norm_nonneg _)
         _ = ∑ i∈U, (V i).budget σ:=by rw [Finset.sum_product]; simp_rw [he]
         _ ≤ _ := (hp.2.1.sum_le_tsum _ (fun i _=>hp.1 i)).trans hp.2.2
    have hb : 0≤ b:=by simpa only [Finset.sum_empty] using hB ∅
    obtain ⟨F,hC,hF⟩:= flashes C (b:=b) (fun S=> by
        calc
         _ ≤ ∑ i∈ S, ‖C i‖*b:= Finset.sum_le_sum fun i hi=> by rw [sq]; gcongr; simpa using hB {i}
         _ ≤ _:=by rw [←Finset.sum_mul,sq]; gcongr; exact hB S) hb
    refine ⟨F,funext fun i=>?_,hF⟩
    have hu: (ringT σ F i).coeff=(V i).coeff:=funext fun k=>by
        unfold ringT; simp only [hC]; rw [show C (i,k)=_ from rfl]; exact mul_div_cancel_left₀ _ (show chants t σ i≠0 from (Real.exp_pos _).ne') -- check
    cases ht: V i with
    | mk x y=>
       rw [ht] at hu
       calc ringT σ F i = ⟨letter i,(ringT σ F i).coeff⟩:=rfl
            _ = _:=by rw [hu]; simp only [← show (V i).leg=letter i from h i, ht]
#check Work.F08.budget_minor
end YM.Stationary.Shade
