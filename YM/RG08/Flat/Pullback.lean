import YM.RG08.Flat.Routing

/-!
# Unchanged rank-two projection through two possibly different backgrounds

Moment order d Taylor-zero lets the repeated part spend d extra fine
forward differences. This bound is on genuine displacement stencils; keeping
one coarse root, not just after periodization. The count L^4 is included.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Finset Laurent Bloch Lattice Matrix Work.F08 RG Precision Next.Free
open scoped Topology BigOperators

variable {α β : Type} {c f L : Side}

lemma row_ext_tail {I : Type} {u : I → Side} {v : Filter I} [v.NeBot]
    (h : Tendsto (fun i => (u i).val) v atTop)
    {A B : Row α β} (ha : A.safe) (hb : B.safe)
    (hp : ∀ᶠ i in v,A.acts (u i) = B.acts (u i)) : A = B := by
  funext i j x
  apply tendsto_nhds_unique ((entry_limit u h A ha i j x).congr'
    (f₂:=fun z => B.acts (u z) (0,i) (wrap (u z) x,j))
    (hp.mono fun k hk => congr_fun (congr_fun hk _) _)) (entry_limit u h B hb ..)

def pullbackRows [Fintype α] (A B : Cross L α β) (D : Row α α) : Row β β :=
  composeRows (transRows A) (fineCompose D B)

section
variable [Fintype α]

lemma pullback_whole {A B : Cross L α β} {D : Row α α}
    (ha : Whole A) (hb : Whole B) (hd : Whole D) : Whole (pullbackRows A B D) :=
    ha.flipped.prod (by
      obtain ⟨s,h₁,hs,H⟩ := hd; obtain ⟨t,h₂,ht,h⟩ := hb
      have he : 0 < min s t := lt_min hs ht
      exact ⟨min s t, _, he, strip_fine he.le
        (strip_mono H (min_le_left ..) le_rfl) (strip_mono h (min_le_right ..) le_rfl)⟩)

lemma pullback_acts (w : Ratio c f) {A B : Cross w.count α β} {D : Row α α}
    (ha : Whole A) (hb : Whole B) (hd : Whole D) :
    (pullbackRows A B D).acts c = (installed w A)ᵀ * D.acts f * installed w B := by
  obtain ⟨s,h₁,hs,H⟩ := hd; obtain ⟨t,h₂,ht,h⟩ := hb
  have he : 0 < min s t := lt_min hs ht
  have hK := strip_mono H (min_le_left s t) le_rfl
  have hL := strip_mono h (min_le_right s t) le_rfl
  rw [pullbackRows,composed_left w ha ⟨_,_,he,strip_fine he.le hK hL⟩,
      installed_fine w he.le hK hL,Matrix.mul_assoc]

end

/-- d=3 gives the L⁻¹ contraction before readout. A, B may have different
 flat history depths; use on the Hessian difference via the cross identity
 rather than bounding a difference of an arbitrarily chosen predictor lift. -/
theorem pullback_gain (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
    (σ τ C : ℝ) (hs : 0 < σ) (ht : 0 < τ) (d : ℕ) :
    ∃ η K : ℝ, 0 < η ∧ η ≤ σ ∧ 0 ≤ K ∧
    ∀ L : Side, Odd L.val → τ ≤ L.val*η → ∀ A B : Cross L α β,
      A.strip τ (C/L.val) →
      (∀ s : List Axis,s.length ≤ d →
        (advanceC L B s).strip τ (C/(L.val:ℝ)^(1+s.length))) →
      ∀ R : Row α α, ∀ M : ℝ, 0 ≤ M → R.strip σ M → ZeroOrder d R →
        (pullbackRows A B R).strip τ (K*M*(L.val:ℝ)^2/(L.val:ℝ)^d) := by
  obtain ⟨η,K,hη,hg,hK,H⟩ := row_division α α d σ hs
  let I := Fin d → Axis
  let m := (Fintype.card α:ℝ)
  let v := (Fintype.card I:ℝ) * m*m*Real.exp (4*τ)*K*C^2
  refine ⟨η,v,hη,hg,by unfold v m; positivity,fun L ho hu A B hA hB R M hm hr hZ => ?_⟩
  let D := (L.val:ℝ)
  have hD : 0 < D := by unfold D; positivity
  obtain ⟨T,hT,hP⟩ := H M hm R hr hZ
  let F (i : I) := fineCompose (T i) (advanceC L B (differenceList i))
  have hF i : (F i).strip τ (m*(Real.exp (4*τ)*(M*K)*(C/D^(1+d)))) := by
    have hh := hB (differenceList i) (difference_length i|>.le)
    rw [difference_length] at hh; exact strip_routed ht.le hu (hT i) hh
  have ha : Whole A := ⟨_,_,ht,hA⟩
  have hb : Whole B := ⟨_,_,ht,hB [] (Nat.zero_le _)⟩
  have hw i : Whole (F i) := ⟨_,_,ht,hF i⟩
  let Y (i : I) := composeRows (transRows A) (F i)
  have hy i : (Y i).strip τ ((D^4*m)*(C/D*(m*(Real.exp (4*τ)*(M*K)*(C/D^(1+d)))))) := by
    rw [show D^4*m=(Fintype.card (Co L α):ℝ) from ?_]
    · exact strip_compose ht.le (strip_trans hA) (hF i)
    unfold D m Co; rw [Fintype.card_prod,site_card]; push_cast; rfl
  have he : pullbackRows A B R=rowSum Y := by
    apply bank_injective (pullback_whole ha hb ⟨_,_,hs,hr⟩).safe
      (rowSum_safe (fun i => Whole.safe ⟨_,_,ht,hy i⟩))
    intro c
    let w : Ratio c (c*L) := ⟨L,rfl⟩
    have hx i : Whole (T i) := ⟨_,_,hη,hT i⟩
    rw [pullback_acts (w:=w) ha hb (show Whole R from ⟨_,_,hs,hr⟩)]
    rw [hP,rowSum_acts (I:=I) (fun i => ((hx i).prod (jet_whole ..)).safe),
        rowSum_acts (I:=I) (fun i => Whole.safe ⟨_,_,ht,hy i⟩),Matrix.mul_sum,
        Matrix.sum_mul]
    refine sum_congr rfl fun j _ => ?_
    have ht' := hB (differenceList j) (difference_length j|>.le)
    have hC : ∀ s : List Axis,s.length ≤ (differenceList j).length → Whole (advanceC L B s) :=
      fun s hp => ⟨_,_,ht,hB _ (hp.trans_eq (difference_length j))⟩
    rw [(hx j).acts (jet_whole ..), show Y j=composeRows (transRows A) (F j) from rfl,
      composed_left w ha (hw j)]
    unfold F
    erw [installed_fine w (lt_min hη ht).le (strip_mono (hT j) (min_le_left η τ) le_rfl)
        (strip_mono ht' (min_le_right η τ) le_rfl), flow_movement w B (differenceList j) ho hC, motion]
    simp only [Matrix.mul_assoc]
  rw [he]
  have hh := rowSum_strip hy
  refine strip_mono hh le_rfl (le_of_eq ?_)
  unfold v
  change _ = _*M*D^2/D^d
  rw [pow_add]; field_simp

end YM.RG08
