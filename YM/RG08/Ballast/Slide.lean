import YM.RG08.Ballast.Pianist
import YM.RG08.Ballast.Ribbons

/-!
# Pre-block soft transfer of aggregate kernel

`σ` input width and `w` output width CAN REQUEST DIFFERENT. `/L`
step-power from full smooth predictions; gradients from difference to tree
must be handled separately. Price relative to any Fourier zero order d, and may
input DIFFERENCES of kernels/grads. No field norm bound implicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function
open UVExt.Paths Stationary Matrix Precision
open scoped Topology ContDiff
variable {α β ι : Type} {r : ℕ} {w σ η C A B : ℝ} {L c f : Side}

section
variable [Fintype α] [Fintype β]

def flow (F : Shale α r) (A : Cross L α β) := score (ribbon (grapes L F) (fun _=>A))
lemma flow_basic {F : Shale α r} {Q : Cross L α β} (hw : 0≤w) (hv : 0≤σ)
    (hx : (r+1:ℕ)*w ≤ L.val*σ) (hy : 0≤B) (hq : Q.strip ((r+1:ℕ)*w) B) (hh : Glow F σ A) :
    Glow (flow F Q) w ((((Fintype.card β:ℝ)*B)^r)*((L.val:ℝ)^4*(Real.exp (4*((r+1:ℕ)*w))^r*A))) ∧ Tunable (flow F Q) ∧
      ∀ c f, ∀ g : Ratio c f, ∀ hb : g.count=L, ∀ v : PAC β c,
        stanza (flow F Q) c v = stanza F f ((installed g (hb.symm ▸ Q))*ᵥ v) := by
  have hb : 0 ≤ ((r+1:ℕ):ℝ)*w := by positivity
  have he := ribbon_price (grapes L F) (fun i : Fin r=>Q) (grapes_glow L hh hb hx) hb (fun _=>hy) (fun _=>hq)
  have hg := he.summable (ling_one hb)
  refine ⟨score_price (by rw [mul_pow]; simpa only [prod_const,card_univ,Fintype.card_fin] using he) hw, score_tunable hg,?_⟩
  intro c f g hv v; subst L
  rw [flow,stanza_score hg]; unfold stanza Tensor.diagonal
  rw [strands _ _ (grapes_glow _ hh hb hx) hb (fun _=>hy) (fun _=>hq), grapes_rec g _ (hh.summable (ling_one (show 0≤σ from ‹_›)))]; rfl

private lemma budget_flow_iter (l : Fin r → List Axis) (L v B : ℝ) :
    ((v^r)*∏ j,(B/L^(1+(l j).length)))=(v*B)^r/L^(r+∑ j,(l j).length) := by
  rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, mul_pow]; simp; ring
end

/-- `Pullback` refined price with width reserve. Applied even on growing
 smoothing transitions. If Ψ lift data not convergent, this does NOT require
 or assert their convergence. -/
theorem flow_soft (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] (r d : ℕ)
    {σ w C : ℝ} (hw : 0<w) (hs : 0<σ) (hc : 0≤C) :
    ∃ η K : ℝ, 0 < η ∧ η ≤ σ ∧ 0 ≤ K ∧ ∀ L : Side,
        Odd L.val → (r+2:ℕ)*w ≤ L.val*η → ∀ (F : Shale α (r+1)) (Q : Cross L α β) (B : ℝ),
        Glow F σ B → ordered F → Dolce d F →
        (∀ i : List Axis,i.length ≤ d → (advanceC L Q i).strip ((r+2:ℕ)*w) (C/(L.val:ℝ)^(1+i.length))) →
      Glow (flow F Q) w ((K*B)*(L.val:ℝ)^4/(L.val:ℝ)^(r+1+d)) := by
  classical
  obtain ⟨η,K,hη,hθ,hK,H⟩ := sostenuto α r d hs
  let j := (Fintype.card β:ℝ)
  let χ : ℝ := (r+2:ℕ)*w
  let W := (j*C)^(r+1)*Real.exp (4*χ)^(r+1)
  let b := (Fintype.card (Breed r α):ℝ)
  let e := (Fintype.card (Fin d→Keys r):ℝ)
  have hp : 0<χ := by unfold χ; positivity
  refine ⟨η, b*e*W*K,hη,hθ,by unfold b e W j; positivity, fun L hL hx F Q B hg ht hV hh=>?_⟩
  have hy : 0<(L.val:ℝ) := by positivity
  obtain ⟨T,hT,Ht⟩ := H F hg ht hV
  let l (v : Fin d→Keys r) := trill (List.ofFn v)
  let p (u : List Axis) := C/(L.val:ℝ)^(1+u.length)
  have hu (u) : 0 ≤ p u := div_nonneg hc (pow_pos hy _).le
  let D v k := advanceC L Q (l v k)
  let R (u : Breed r α) (v) := ribbon (grapes L (T u v)) (D v)
  let z := W*K*B*(L.val:ℝ)^4/(L.val:ℝ)^(r+1+d)
  have hℓ (u v) : Glow (R u v) χ z := by
    have hw := ribbon_price (grapes L (T u v)) _ (grapes_glow L (hT u v) hp.le hx) hp.le
      (fun k => hu (l v k)) (show ∀ i, (D v i).strip χ (p (l v i)) from fun i => hh _ (trill_bound v i))
    apply glow_less hw le_rfl (le_of_eq ?_); unfold z W p l at *
    simp only [budget_flow_iter, trill_count,List.length_ofFn]; unfold j; dsimp only [χ]; ring
  have hQ : Q.strip χ (p []) := hh [] (Nat.zero_le _)
  have hv := flow_basic hw.le hs.le (hx.trans (mul_le_mul_of_nonneg_left hθ hy.le)) (hu []) hQ hg
  apply reword_price (H:=∑ u : Breed r α, ∑ v, R u v) hv.2.1 _ hw.le
  · intro m
    let g : Ratio m (m*L) := ⟨L,rfl⟩
    funext y
    have hb (u v) : Summable (R u v) := (hℓ u v).summable (ling_one hp.le)
    rw [hv.2.2 m _ g rfl y,stanza_sum _ _ (fun u _=> shale_total_sum _ fun v _=> hb u v),Finset.sum_apply,stanza,Tensor.diagonal, Ht]
    apply sum_congr rfl; intro u _; rw [stanza_sum _ _ (fun v _=> hb u v),Finset.sum_apply]; apply sum_congr rfl; intro v _
    let U := T u v
    have H i : motion α (m*L) (l v i)*installed g Q = installed g (D v i) := by
      have hJ := trill_bound v i
      exact (flow_movement g Q (l v i) hL (fun j hj=> ⟨_,_,hp,hh j (hj.trans hJ)⟩)).symm
    change recital U _ (fun j => motion α (m*L) (l v j)*ᵥ (installed g Q *ᵥ y))=recital (R u v) m (fun _=> y)
    simp_rw [mulVec_mulVec, H]; unfold R; rw [strands _ _ (grapes_glow L (hT u v) hp.le hx) hp.le (fun i=> hu (l v i)) (fun i=>show (D v i).strip χ (p _) from hh _ (trill_bound v i)),grapes_rec g _ ((hT u v).summable (ling_one hη.le))]; rfl
  have hz := Charge.sums (s:=univ) (w:=ling χ) (fun i => (ling_pos χ _).le) (fun i _ => Charge.sums (s:=univ) (w:=ling χ) (fun i => (ling_pos χ _).le) (fun v _=> hℓ i v))
  simp only [sum_const,card_univ,nsmul_eq_mul] at hz
  apply glow_less hz le_rfl (le_of_eq ?_); unfold z b e; ring
end YM.RG08
