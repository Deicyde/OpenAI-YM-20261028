import YM.Corona.Fill
/-! Traverse spanning nodes without support multiplicity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Lattice.Corona
open Relation
variable {n : Side}

private lemma enlarge {R : ℕ → Site n} {N a i y b} (hh : ∀ k < N, separation (R k) (R (k+1)) ≤ 1) (hi : i ≤ N) (ht : R i=a)
    (hy : separation a y ≤ b) : ∃ S : ℕ → Site n, (∀ k < N+b+b,separation (S k) (S (k+1))≤1) ∧
    (∀ j≤N,∃ k≤N+b+b, S k = R j) ∧ ∃ k≤N+b+b,S k=y := by
  let S := fun k => if k ≤ i then R k else if k ≤ i+b then line a y (k-i) else if k ≤ i+b+b then
    line a y (i+b+b-k) else R (k-(b+b))
  have ha (k) (hk : k ≤ i) : S k=R k := if_pos hk
  have hb (k) (hk : i≤k) (he : k≤ i+b) : S k = line a y (k-i) := by
    if h : k=i then subst k; rw [ha _ le_rfl,Nat.sub_self,line_home,ht]
    else simp only [S,if_neg (show ¬ k≤ i by omega),if_pos he]
  have hc (k) (hk : i+b≤k) (he : k≤ i+b+b) : S k=line a y (i+b+b-k) := by
    if h : k=i+b then subst k; rw [hb _ (by omega) le_rfl]; congr 1; omega
    else simp only [S,if_neg (show ¬ k≤ i by omega),if_neg (show ¬ k≤ i+b by omega),if_pos he]
  have hd (k) (hk : i+b+b≤k) : S k=R (k-(b+b)) := by
    if h : k=i+b+b then subst k; rw [hc _ (by omega) le_rfl,Nat.sub_self, line_home,show i+b+b-(b+b) = i by omega, ht]
    else simp only [S,if_neg (show ¬ k≤ i by omega),if_neg (show ¬ k≤ i+b by omega),if_neg (show ¬ k≤ i+b+b by omega)]
  refine ⟨S,fun k hk => ?_,fun j hj => ?_, i+b, by omega,by rw [hb _ (by omega) le_rfl,Nat.add_sub_cancel_left, line_end _ _ hy]⟩
  · by_cases hx : k< i
    · rw [ha _ (by omega),ha _ (by omega)]; exact hh k (hx.trans_le hi)
    by_cases he : k< i+b
    · rw [hb _ (by omega) (by omega),hb _ (by omega) (by omega)]
      exact (line_dist a y _ _ (by omega)).trans (by omega)
    by_cases h : k < i+b+b
    · rw [hc _ (by omega) (by omega),hc _ (by omega) (by omega),separation_comm]
      exact (line_dist a y _ _ (by omega)).trans (by omega)
    rw [hd _ (by omega),hd _ (by omega),show k+1-(b+b)=k-(b+b)+1 by omega]; exact hh _ (by omega)
  by_cases h : j≤ i
  · exact ⟨j,by omega,ha j h⟩
  exact ⟨j+b+b,by omega,by rw [hd _ (by omega), show j+b+b-(b+b)=j by omega]⟩

lemma ring_path {D : Support n} (b : ℕ) (hh : Ships D b) : ∃ N : ℕ,N ≤ D.card*(b+b) ∧ ∃ R : ℕ → Site n,
    (∀ k < N,separation (R k) (R (k+1))≤1) ∧ ∀ i∈D,∃ k≤N,R k=i := by
  classical
  by_cases hw : D.Nonempty
  · have h : ∀ a : ℕ, a+1 ≤ D.card → ∃ U ⊆ D,U.card=a+1 ∧ ∃ R : ℕ → Site n,
        (∀ k < a*(b+b),separation (R k) (R (k+1)) ≤ 1) ∧ ∀ i∈U,∃ k≤a*(b+b),R k=i := by
      intro a; induction a with
      | zero =>
        rintro -; obtain ⟨x,hx⟩ := hw
        exact ⟨{x},by simp [hx],by simp,fun _ => x,by simp,by simp⟩
      | succ a ih =>
        intro hsz
        obtain ⟨U,hUD,hU,R,hr,hR⟩ := ih (by omega)
        obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
        obtain ⟨y,hD,hy⟩ := Finset.exists_mem_notMem_of_card_lt_card (show U.card<D.card by omega)
        have he : ∀ j, ReflTransGen (Touch D b) x j → j ∉ U → ∃ l∈U,∃ k∈D,k∉U ∧ separation l k ≤ b := by
          intro j H; induction H with
          | refl => exact fun he => absurd hx he
          | @tail l k _ hj IH =>
            intro hK
            by_cases h : l∈U
            · exact ⟨l,h,k,hj.2.1,hK,hj.2.2⟩
            exact IH h
        obtain ⟨l,hl,k,hk,hK,hse⟩ := he y (hh x (hUD hx) y hD) hy
        obtain ⟨i,hi,hR'⟩ := hR l hl
        obtain ⟨S,hS,hs,h'⟩ := enlarge hr hi hR' hse
        have hj : (a+1)*(b+b)=a*(b+b)+b+b := by rw [Nat.add_mul, Nat.one_mul,Nat.add_assoc]
        rw [hj]; refine ⟨insert k U, Finset.insert_subset hk hUD,by rw [Finset.card_insert_of_notMem hK,hU],S,hS,?_⟩
        intro x hx; rcases Finset.mem_insert.mp hx with rfl|hv
        · exact h'
        obtain ⟨m,hm,hz⟩ := hR x hv; rw [← hz]; exact hs m hm
    obtain ⟨a,ha⟩ := Nat.exists_eq_add_one.mpr (Finset.card_pos.mpr hw)
    obtain ⟨U,h1,hU,R,hr,H⟩ := h a ha.ge
    rw [Finset.eq_of_subset_of_card_le h1 (ha ▸ hU.ge)] at H
    exact ⟨_, by gcongr; omega,R,hr,H⟩
  refine ⟨0,Nat.zero_le _,fun _ => 0,by simp,?_⟩
  rw [Finset.not_nonempty_iff_eq_empty.mp hw]; simp

lemma path_span {R : ℕ → Site n} {N : ℕ} (hh : ∀ k < N,separation (R k) (R (k+1)) ≤ 1) : ∀ i j, i≤j → j≤N → separation (R i) (R j) ≤ j-i := by
  rintro i j hj
  induction j,hj using Nat.le_induction with
  | base => simp
  | succ j hj IH =>
    intro hk
    exact (separation_triangle (R i) (R j) _).trans (by specialize IH (by omega); have := hh j hk; omega)

lemma extent (X : Support n) (M : ℕ) {x y} (hx : x∈X) (hy : y∈X) :
    separation x y ≤ coverNumber M X * (4*M+2)+2*M := by
  obtain ⟨D,H,h1⟩ := coverNumber_realized M X; rw [← h1]
  obtain ⟨N,hN,R,hR,hh⟩ := ring_path _ (halo_ship _ H.2)
  obtain ⟨a,ha,he⟩ := halo_spec.mp (H.1 hx); obtain ⟨b,hb,hf⟩ := halo_spec.mp (H.1 hy)
  have h : separation a b ≤ N := by
    obtain ⟨i,hi,hg⟩ := hh a ha; obtain ⟨j,hj,hg'⟩ := hh b hb; rw [← hg,← hg']
    rcases le_total i j with H|H
    · exact (path_span hR _ _ H hj).trans (by omega)
    rw [separation_comm]; exact (path_span hR _ _ H hi).trans (by omega)
  have hh1 := separation_triangle a b y; have hh2 := separation_triangle x a y; rw [separation_comm x a] at hh2
  rw [show M+M+1+(M+M+1)=4*M+2 by omega] at hN; omega
end YM.Lattice.Corona
