import YM.FullVolume.Regent.Springs
/-! Perimeter receptive norms.Pop natural waves.IT. Vanishing when exact lease. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.ConeRay
open Lattice RG Precision Wilson Filter Function Laurent Bloch Exterior Finset
open Matrix (transpose mulVec of)
open scoped Matrix Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n:Side}
abbrev Twist (G:Gauge):= TypeFace 1→G.ColorIndex→ℂ
def Toss (b:ℝ)(F: Tensor.T (Link G n) ℝ 2):Prop:=∀ p q (u v:Twist G), (∀ i j,‖u i j‖≤1)→ (∀ i j, ‖v i j‖≤1)→ |F ![pew p u,pew q v]|≤ cents n*b
-- basis decomposition recover Glyph.Jet exact using complex
private def coin (x: Loc G 1)(s:ℂ) : Twist G:=fun i j=>(Pi.single x s:Loc G 1→ℂ) (i,j)
private lemma spent (p:Site n)(x: Loc G 1)(i:Lines G n 1)(s:ℂ): pew p (coin x s) i= (s*relay p x i).re:=by
    rcases i with ⟨i,j,k⟩; change (cell p i * coin x s j k).re=(s*relay p x (i,j,k)).re
    unfold coin relay tune; dsimp only
    by_cases h:(j,k)=x <;> simp only [Pi.single_apply,h,↓reduceIte] <;> simp_all [mul_comm]
private lemma consumes (x: Loc G 1)(s:ℂ)(hs:‖s‖≤1) i j: ‖coin x s i j‖≤1:=by by_cases h:(i,j)=x <;> simp [coin,h,hs]
private def ka : Fin 2→ℂ:=![1,Complex.I]
private def qi : Fin 2→ℂ:=![1,-Complex.I]
private lemma decodes (p:Site n)(x:Loc G 1): relay p x=∑ j:Fin 2,ka j • axes (pew p (coin x (qi j))):=by
     funext i; simp only [Fin.sum_univ_two,ka,qi,Pi.add_apply,Pi.smul_apply,smul_eq_mul,axes,spent]; apply Complex.ext <;> simp
lemma fare (F: Link G n→ℝ){b:ℝ}(hb:0≤b)(h:Toss b (iteratedFDeriv ℝ 2 F 0)) (p:Fin (1+1)→Site n)(x: Ink G (1+1)) (i:Run (1+1)): ‖noteAt F 2 (glyph p x i)‖ ≤ cents n * (4*b):=by
    let g j k := pew (p j) (coin (i j,x j) (qi k)); let H j k:= ka k • axes (g j k)
    have hz : glyph p x i=fun j=>∑ k,H j k:=funext fun j=> decodes _ _
    have hh v : ‖noteAt F 2 (axes ∘ v)‖ = (2:ℝ)⁻¹ * ‖iteratedFDeriv ℝ 2 F 0 v‖:=by rw [note_real]; simp [Tensor.coeff,Nat.factorial]
    rw [hz, MultilinearMap.map_sum (g:=H)]
    calc
      _ ≤ _:=norm_sum_le ..
      _ ≤ ∑ _ : Fin 2→Fin 2, cents n*b :=by
            apply sum_le_sum; intro z _
            rw [show noteAt F 2 (fun i=> H i (z i))= _ from (noteAt F 2).map_smul_univ (fun j=>ka (z j)) (axes ∘ (fun j=>g j (z j))),norm_smul, hh]
            have ht (j):‖ka j‖=1:=by fin_cases j <;> simp [ka]
            rw [norm_prod]; simp_rw [ht,prod_const_one,one_mul]
            have hv j:‖qi j‖≤1 := by fin_cases j <;> simp [qi]
            apply (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans
            rw [show (fun j=> g j (z j))=![g 0 (z 0),g 1 (z 1)] from funext (fun j => by fin_cases j <;> rfl)]; exact h _ _ _ _ (consumes _ _ (hv _)) (consumes _ _ (hv _))
      _ = _:=by simp; ring

variable {m:ℕ→Side}
abbrev Words (m:ℕ→Side)(G:Gauge):=∀ i,Link G (m i)→ℝ
structure High (m:ℕ→Side)(g : ∀ i,Tensor.T (Link G (m i)) ℝ 2):Prop where
    proceeds:∃ b:ℕ→ℝ,(∀ x,0≤ b x)∧ Tendsto b atTop (𝓝 0) ∧ ∀ i,Toss (b i) (g i)
abbrev Tall (f:Words m G):= High m fun i=> iteratedFDeriv ℝ 2 (f i) 0
lemma roared {Q: Picture G 1}{F:Words m G}{σ A:ℝ}(hp:Tall F)(h:Tendsto (fun i=>(m i).val) atTop atTop)
    (he:∀ i j, Firm σ A (Q i j)) (hc:∀ i, Recorded Q (F i) 0): (∀ i j p,Q i j (axes p)=0)∧ ∀ i,iteratedFDeriv ℝ 2 (F i) 0=0:=by
    have he' i : Recorded Q (F i) (cents (m i)*(fun _=> (0:ℝ)) i):=by rw [mul_zero]; exact hc i
    have hh (x j p): Q x j (axes p)=0:=by
         obtain ⟨b,hb,H'⟩:=hp.proceeds; obtain ⟨u,r,H,Q'⟩:= Stationary.fleet m h (axes p) (axes_real p)
         apply tendsto_nhds_unique (harvest he he' tendsto_const_nhds p u r H Q' x j)
         rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun i=>norm_nonneg _) ?_ (show Tendsto (fun i=>4*b i) atTop (𝓝 0) from by simpa using H'.1.const_mul 4)
         intro i; unfold standing; rw [norm_mul,norm_inv, Complex.norm_real, Real.norm_of_nonneg cents_pos.le]; exact (mul_le_mul_of_nonneg_left (fare _ (hb i) (H'.2 i) _ _ _) (inv_nonneg.mpr cents_pos.le)).trans_eq (inv_mul_cancel_left₀ cents_pos.ne' _)
    refine ⟨hh,fun i=>?_⟩
    have hf : aperture 0 (F i) (fun _=>0) 1:=by
        intro p j b g; unfold g; rw [(record_exact ..).1 (hc i)]; have hX : noteAt (fun _:Link G (m i)=> (0:ℝ)) (1+1)=0:=by
             unfold noteAt beat; have hx: iteratedFDeriv ℝ (1+1) (fun _:Link G (m i)=> (0:ℝ)) 0=0:=by simp [iteratedFDeriv_succ_const]
             rw [hx]; apply MultilinearMap.ext; intro w; simp [enlarge, recording_apply]
        rw [hX]; unfold collected; have ht: Q j b (outphase p)=0:=by rw [← axes_of_real (out_real p), hh]
        split <;> simp [ht]
    have hY := aperture_eq hf; exact hY.trans (by simp [iteratedFDeriv_succ_const])
end YM.Stationary.ConeRay
