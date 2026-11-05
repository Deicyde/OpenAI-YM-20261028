import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Edit

set_option warningAsError false

/-! # Calculate the repairs explicitly, at any relevant arity -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet
open RG Marker Wilson Lattice Multi Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {V : Type} [DecidableEq V] {R : Census V}

/-- If removing s from an actual query in the sector, the intermediate
query is still permitted by the Census.
-/
def dim (s : V) (x : R.Mode) : R.Mode := ⟨x.val.erase s,R.down x.property _ (Finset.erase_subset ..)⟩

theorem marked_part (s : V) (f : Poly R) (x : R.Mode) : ((Poly.send (R.fire s) 1)*f).part x=
    if s∈ x.val then f.part (dim s x) else 0 := by
  rw [Poly.part_mul, Finset.sum_eq_single (R.fire s)]
  · have hh (i : R.Mode) : Poly.merges (R.fire s) i x ↔ s∈x.val ∧ i=dim s x := by
      change Disjoint ({s}:Finset V) i.val ∧ {s}∪i.val=x.val ↔ _
      rw [singleton_union,Finset.disjoint_singleton_left]
      constructor
      · rintro ⟨he,hH⟩; refine ⟨hH ▸ mem_insert_self .., Subtype.ext ?_⟩
        change _=x.val.erase _; rw [← hH,Finset.erase_insert he]
      rintro ⟨hi,rfl⟩; exact ⟨Finset.notMem_erase _ _,Finset.insert_erase hi⟩
    simp_rw [hh]; by_cases h : s∈x.val <;> simp [h]
  · intro i _ hi; simp only [Poly.part_send,if_neg hi,zero_mul,ite_self,sum_const_zero]
  simp

variable {G : Gauge} {n : Side} (P : Rep G n) (s : V)
variable (D : Hot R → Pulse G n) (p : Pack n) (z : Site n) (F : Config G n → ℂ)

private lemma subtract (f g : Poly R) (i : R.Mode) : (f-g).part i=f.part i-g.part i := by rw [sub_eq_add_neg,sub_eq_add_neg,Poly.part_plus, Poly.part_neg]

private lemma ink_part (r : Pack n) (W : Config G n → Poly R) (i : R.Mode) (U : Config G n) : (ink P U p r W).part i=
    (soloPay p (shielded P p (fun U => (W U).part i))).2 r U := by
  by_cases he : r=p
  · unfold ink soloPay shielded; simp only [if_pos he]; split <;> simp [*]
  unfold ink soloPay; simp only [if_neg he,Poly.part_nil]; rfl

private lemma pen_part (r : Pack n) (i : R.Mode) (U : Config G n) : (pen (R:=R) U p F r).part i=
    if i=R.quiet then (soloPay p F).2 r U else 0 := by
  by_cases h : r=p
  · unfold pen soloPay; simp only [if_pos h]; exact Poly.part_send ..
  unfold pen soloPay; simp only [if_neg h, Poly.part_nil]; split <;> rfl

/-- Exactly the desired reindexing of singleton F inputs AFTER the coarse
step. Higher-mode repair below. Thus usable with a one-step lemma retaining
the matched primary M UP TO these nullPay expansions.
-/
theorem edited_at : edited P s D p z F (Hot.one R s) = D (Hot.one R s)+nullPay P p z F := by
  apply Prod.ext
  · unfold nullPay enlarged soloPay edited; simp [Prod.fst_sum]
  funext r U
  change (D _).2 r U + _=(D _).2 r U+_
  congr 1
  unfold supplement; rw [marked_part,if_pos (show s ∈ (Hot.one R s).val.val from mem_singleton_self _)]
  rw [show dim s (Hot.one R s).val = R.quiet from (show dim s (R.fire s)=_ from Subtype.ext (by simp [Census.fire,dim,Census.quiet]))]
  unfold nullPay enlarged alteration
  simp_rw [subtract,Poly.part_plus,Poly.part_sum,ink_part P,pen_part,if_true,
    Prod.snd_sub,Prod.snd_add,Prod.snd_sum,Pi.sub_apply,Pi.add_apply,Finset.sum_apply]
  have h₁ (u : ℂ) : (algebraMap ℂ (Poly R) u).part R.quiet = u := by change (Poly.send _ u).part _ = _; simp
  simp_rw [Poly.quiet_mul,h₁,share_quiet]

theorem dormant (x : Hot R) (h : s∉x.sites) : edited P s D p z F x = D x := by
  refine Prod.ext rfl ?_; funext r U; unfold edited supplement; dsimp only; rw [marked_part,if_neg h,add_zero]

/-- Valid depth-pricing case: s occurs in x but has at least one other
marker with it. -/
theorem spark (x i : Hot R) (h : s∈x.sites) (hI : i.sites=x.sites.erase s) :
    edited P s D p z F x=D x-∑ j∈attaches p z, soloPay (braid p j) (shielded P (braid p j)
      (fun v => F v*(D i).2 j v)) := by
  have he : dim s x.val=i.val := Subtype.ext hI.symm
  apply Prod.ext
  · unfold edited soloPay; simp [Prod.fst_sum]
  funext r v; unfold edited supplement alteration; dsimp only
  rw [marked_part,if_pos h,he]
  simp_rw [subtract, Poly.part_plus,Poly.part_sum,pen_part,if_neg (show i.val≠R.quiet from fun he => by
    have hp := i.property; rw [he] at hp; exact not_nonempty_empty hp),ink_part P]
  have hs c (Y : Poly R) : (algebraMap ℂ _ c *Y).part i.val = c*Y.part i.val := by rw [← Algebra.smul_def]; exact Poly.part_smul ..
  have hr (c : ℂ) : (algebraMap ℂ (Poly R) c).part i.val=0 := by
    change (Poly.send _ c).part _ = _; rw [Poly.part_send,if_neg]; intro h; obtain hm:=i.property; rw [h] at hm; exact not_nonempty_empty hm
  simp_rw [Prod.snd_sub,Prod.snd_sum,Pi.sub_apply,Finset.sum_apply,hs,share_at (R:=R),hr]
  simp only [soloPay,shielded, ite_self,ite_apply, Pi.zero_apply,zero_add,sub_eq_add_neg]
end YM.AnalyticNext.GridStop.Alphabet
