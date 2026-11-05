import YM.Work.I01


/-! Estimate among many separated marker keys by a visit tour *on the torus*. -/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Marker Lattice Function Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {R : Census V}
variable {n : Side}

namespace Convoy

def miles (f : V → Site n) (p : V) (l : List V) : ℕ := match l with
  | [] => 0
  | x::t => separation (f p) (f x) + miles f x t

private lemma from_time (f : V → Site n) (S : Finset V) {B N : ℕ}
    (r : ℕ → Site n) (w : V → ℕ) (p : V) (h : ∀ k < N, separation (r k) (r (k+1)) ≤ 1)
    (hp : w p ≤ N) (hv : separation (r (w p)) (f p) ≤ B)
    (hh : ∀ i ∈ S, i≠p ∧ w p≤w i ∧ w i ≤ N ∧ separation (r (w i)) (f i) ≤ B) :
    ∃ l : List V, (p::l).Nodup ∧ l.toFinset=S ∧
      miles f p l + w p ≤ S.card * (2*B) + N := by
  by_cases e : S.Nonempty
  · obtain ⟨x,hx,he⟩ := exists_min_image S w e
    obtain ⟨h₀,ht,hs,hw⟩ := hh x hx
    obtain ⟨l,H,H',hy⟩ := from_time f (S.erase x) r w x h hs hw (fun i hi =>
      ⟨(mem_erase.mp hi).1, he _ (mem_of_mem_erase hi), (hh _ (mem_of_mem_erase hi)).2.2⟩)
    refine ⟨x :: l,List.nodup_cons.mpr ⟨?_,H⟩, ?_,?_⟩
    · rw [List.mem_cons, ← List.mem_toFinset, H']
      rintro (he|hf)
      · exact h₀ he.symm
      exact (hh p (mem_of_mem_erase hf)).1 rfl
    · simp only [List.toFinset_cons,H',insert_erase hx]
    have hf := Corona.path_span h _ _ ht hs
    have h1 := separation_triangle (f p) (r (w p)) (f x)
    have h2 := separation_triangle (r (w p)) (r (w x)) (f x)
    rw [separation_comm (f p) (r (w p))] at h1
    rw [show S.card=(S.erase x).card+1 by rw [card_erase_add_one hx], Nat.add_mul, one_mul, miles]
    omega
  rw [Finset.not_nonempty_iff_eq_empty.mp e]
  exact ⟨[], by simp, by simp, by simpa [miles] using hp⟩
termination_by S.card
 decreasing_by exact card_erase_lt_of_mem hx

lemma routed {V : Type} [Fintype V] [DecidableEq V] (f : V → Site n) (S : Finset V) {B : ℕ}
    (hB : 8 ≤ B) (p : V) (hp : p∈ S) (hk : 2 ≤ S.card)
    (hq : ∀ i∈S,∀ j∈S,i≠j → B^2 ≤ separation (f i) (f j)) :
    ∃ l : List V, l ≠ [] ∧ (p::l).Nodup ∧ (p::l).toFinset=S ∧
      miles f p l ≤ (256*B)*coverNumber B (S.image f) := by
  obtain ⟨D,hD,hc⟩ := coverNumber_realized B (S.image f)
  obtain ⟨N,hn,r,hr,ht⟩ := Corona.ring_path _ (Corona.halo_ship B hD.2)
  have hw (i : V) (hi : i∈S) : ∃ k≤N, separation (r k) (f i) ≤ B := by
    obtain ⟨v,hv,H⟩ := halo_spec.mp (hD.1 (mem_image_of_mem f hi))
    obtain ⟨k,hk,hK⟩ := ht v hv
    exact ⟨k,hk,hK ▸ H⟩
  choose! t hw hh using hw
  have he : (S.erase p).Nonempty := card_pos.mp (by rw [card_erase_of_mem hp]; omega)
  obtain ⟨x,hx,hs⟩ := exists_min_image _ t he
  have h := (Finset.mem_erase.mp hx).1
  have hv := mem_of_mem_erase hx
  obtain ⟨l,hl,H,h₁⟩ := from_time f ((S.erase p).erase x) r t x hr (hw _ hv) (hh _ hv)
    (fun i hi => ⟨(mem_erase.mp hi).1, hs _ (mem_of_mem_erase hi), hw _ (by
      exact mem_of_mem_erase (mem_of_mem_erase hi)), hh _ (by exact mem_of_mem_erase (mem_of_mem_erase hi))⟩)
  have HC : (x::l).toFinset=S.erase p := by simp [H,hx]
  refine ⟨x::l, by simp,List.nodup_cons.mpr ⟨by rw [← List.mem_toFinset,HC]; simp,hl⟩,
    by rw [List.toFinset_cons,HC,insert_erase hp],?_⟩
  have hd : separation (r (t p)) (r (t x)) ≤ N := by
    rcases le_total (t p) (t x) with h | h
    · exact (Corona.path_span hr _ _ h (hw _ hv)).trans ((Nat.sub_le ..).trans (hw _ hv))
    rw [separation_comm]; exact (Corona.path_span hr _ _ h (hw _ hp)).trans ((Nat.sub_le ..).trans (hw _ hp))
  have HF : separation (f p) (f x) ≤ 2*B+N := by
    have h1 := separation_triangle (f p) (r (t p)) (f x)
    have h2 := separation_triangle (r (t p)) (r (t x)) (f x)
    rw [separation_comm (f p) (r (t p))] at h1
    have := hh _ hv; have := hh _ hp; omega
  rw [miles, ← hc]
  have HT : B*S.card≤64*D.card := hc ▸ Work.I01.answer n V f B hB S hq hk (S.image f) le_rfl
  have HY : separation (f p) (f x)+miles f x l ≤ 2*(B*S.card)+2*N := by
    have ha := Finset.card_erase_add_one hx; have HB := Finset.card_erase_add_one hp
    have hr : 2*(B*S.card) = ((S.erase p).erase x).card * (2*B)+2*B+2*B := by rw [← HB, ← ha]; ring
    omega
  refine HY.trans ?_
  have hN : N ≤ D.card*(6*B) := hn.trans (Nat.mul_le_mul_left _ (by omega))
  nlinarith
end Convoy
end YM.Multi
