import YM.Corona.Fit
import YM.Corona.Halo
import YM.Lattice.Subdivision
/-!
# Coarsening costs, 

Pre-L shape. Can include flags halo, large projected K etc without
cost depending on period. Does NOT assert that a kernel transformation
needs no more reads than this stencil. That's a separate producer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Lattice.Corona
open Relation
variable {m n : Side} (q : Ratio m n)

lemma near (x : Site n) : 2*separation x (q.embed (q.parent x)) ≤ q.count.val := by
  unfold separation
  rw [show x-q.embed _ = wrap n (lift (q.residue x)) by nth_rewrite 1 [← q.unpack_at x]; abel]
  have he : pdist (wrap n (lift (q.residue x))) ≤ q.count.val/2 := Finset.sup_le fun i _ => (lap ..).trans
    (ZMod.natAbs_valMinAbs_le _)
  omega

lemma below (x y : Site m) : q.count.val*separation x y ≤ separation (q.embed x) (q.embed y) := by
  unfold separation
  rw [← q.root_embed,← q.root_embed,← map_sub, q.root_embed]
  obtain ⟨i,-,hx⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun i => (lift (x-y) i).natAbs)
  apply le_trans _ (component_le (q.embed (x-y)) i)
  rw [q.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]
  exact le_of_eq (congr_arg (q.count.val*·) (show pdist (x-y) = _ from hx))

lemma foreshorten (x y : Site n) : q.count.val*separation (q.parent x) (q.parent y) ≤ separation x y+q.count.val := by
  apply (below q _ _).trans
  apply (separation_triangle _ x _).trans
  rw [separation_comm _ x]
  have hx := near q x; have hy := near q y; have hz := separation_triangle x y (q.embed (q.parent y)); omega

lemma fuel (R : ℕ → Site n) (N : ℕ) (h : ∀ k < N,separation (R k) (R (k+1)) ≤ 1)
    (M : ℕ) (hp : 0 < M) : ∃ D : Support m, Ships D (2*M) ∧ q.count.val*M*D.card ≤ N+q.count.val*M ∧
    ∀ k ≤ N, q.parent (R k)∈halo (2*M) D := by
  let R' := q.count.val*M
  have he : 0 < q.count.val := q.count.property
  have hg : 0 < R' := Nat.mul_pos he hp
  let F := fun k => q.parent (R (R'*k))
  let D := (Finset.range (N/R'+1)).image F
  have hr (i) : i ≤ N/R' → R'*i ≤ N := fun hi => by
    rw [mul_comm]; exact (Nat.le_div_iff_mul_le hg).mp hi
  have hn (a b) (hh : a ≤ b) (h1 : b ≤ N) (h2 : b-a ≤ R') : separation (q.parent (R a)) (q.parent (R b)) ≤ 2*M := by
    apply Nat.le_of_mul_le_mul_left _ he
    calc
      _ ≤ _ := foreshorten q _ _
      _ ≤ R'+q.count.val := Nat.add_le_add_right ((path_span h a b hh h1).trans h2) _
      _ ≤ _ := by dsimp [R']; nlinarith only [he,hp]
  have hy (i) (hi : i ≤ N/R') : ReflTransGen (Touch D (2*M)) (F 0) (F i) := by
    apply line_path
    · intro j hj; exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
    intro j hj
    refine hn _ _ ?_ (hr _ (by omega)) ?_ <;> rw [Nat.mul_succ] <;> omega
  refine ⟨D,fun i hi j hj ↦ ?_,?_,fun k hk => ?_⟩
  · obtain ⟨i,h1,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j,h2,rfl⟩ := Finset.mem_image.mp hj
    exact (sym (hy i (Nat.lt_succ_iff.mp (Finset.mem_range.mp h1)))).trans
      (hy j (Nat.lt_succ_iff.mp (Finset.mem_range.mp h2)))
  · have hu : D.card ≤ N/R'+1 := by apply Finset.card_image_le.trans; rw [Finset.card_range]
    apply (Nat.mul_le_mul_left R' hu).trans
    rw [Nat.mul_succ]; exact Nat.add_le_add_right (hr _ le_rfl) _
  have h1 := Nat.mod_add_div k R'
  have h2 := Nat.mod_lt k hg
  have hk' := Nat.div_le_div_right (c:=R') hk
  exact halo_spec.mpr ⟨_,Finset.mem_image_of_mem F (Finset.mem_range.mpr (show k/R'<N/R'+1 by omega)),hn (R'*(k/R')) k (by omega) hk (by omega)⟩

/-- Explicit Fproj with full halo price. Incident shifts can use some B's from s. -/
lemma collapse (X : Support n) (M B : ℕ) (h : 0 < B) (hp : M ≤ 2*B) (s : ℕ) :
    q.count.val*coverNumber B (halo (s*B) (X.image q.parent)) ≤
      (q.count.val+10*coverNumber M X)*((s+6)+(s+6)+1)^4 := by
  let Y := halo (s*B) (X.image q.parent)
  obtain ⟨A,H,hA⟩ := coverNumber_realized M X
  obtain ⟨N,hN,R,Hr,HH⟩ := ring_path _ (halo_ship M H.2)
  obtain ⟨D,Hs,Hy,Hf⟩ := fuel q R N Hr B h
  have hw : covers ((s+5)*B) Y D := by
    refine ⟨fun i hi ↦ ?_,ship_halo _ (fun i hi j hj => ReflTransGen.mono (fun x y (h : Touch D (2*B) x y) => ⟨h.1,h.2.1,h.2.2.trans (by simp only [Nat.add_mul]; omega)⟩) i j (Hs _ hi _ hj))⟩
    obtain ⟨a,ha,h1⟩ := halo_spec.mp hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨c,hc,h2⟩ := halo_spec.mp (H.1 hv)
    obtain ⟨k,hk,hh⟩ := HH c hc
    have hj := Hf k hk; rw [hh] at hj
    obtain ⟨j,hm,h3⟩ := halo_spec.mp hj
    apply halo_spec.mpr; refine ⟨j,hm,?_⟩
    have hl : 0 < q.count.val := q.count.property
    have he : separation (q.parent c) (q.parent v) ≤ 3*B := by
      refine Nat.le_of_mul_le_mul_left ((foreshorten q c v).trans ?_) hl
      nlinarith only [h,h2, hp, hl]
    have ht := separation_triangle j (q.parent c) (q.parent v); have hz := separation_triangle j (q.parent v) i
    simp only [Nat.add_mul]; omega
  have he := tiling h hw
  apply (Nat.mul_le_mul_left q.count.val he).trans
  rw [← Nat.mul_assoc]
  refine Nat.mul_le_mul_right _ ?_
  rw [← hA]; apply Nat.le_of_mul_le_mul_left _ h
  rw [show B*(q.count.val*D.card)= q.count.val*B*D.card by ring]
  refine Hy.trans (le_trans (Nat.add_le_add_right hN _) ?_)
  rcases A.eq_empty_or_nonempty with ha|ha
  · simp [ha,mul_comm]
  have hK := Finset.card_pos.mpr ha
  nlinarith only [hK,h,hp]
end YM.Lattice.Corona
