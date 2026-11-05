import YM.Extra.MULTISOURCE_BOUNDS.LogTerms
import YM.Next.BOUNDARY.Alias

/-!
# Unnumbered, potentially repeated marked composites 

For example negative copies of the omitted cluster occurrences may repeat,
forced or (nonempty) square-free source addresses may not. Normalization
uses the ACTUAL occurrence counts. Topological hypothesis is connectivity
via overlap of complete supports. A `Display` is a product bound per charged
output address plus multiplicity account (not equality of density formulas).
This count also works for downstream requests for dollar prices at larger
exponents. Threshold check needed before each use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.Merger
open Function Filter Lattice Wilson RG Finset Overlay Marker Repeated Mayer LogTerms
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {α β ι V : Type*} {n : Side}

open Numbered in
lemma divisor_map {m : Multiset α} {f : α → β} (hf : Injective f) : Numbered.divisor (m.map f) = Numbered.divisor m := by
  -- divisor, toFinset instances are pinned (not the structural Decidable instances on e.g. sigma).
  unfold Numbered.divisor; rw [Multiset.toFinset_map, prod_image hf.injOn]; simp_rw [Multiset.count_map_eq_count' f m hf]

private lemma expand_sum (P : Multiset α → ℝ) (A : Finset α) (V : Type) [Fintype V] :
    ∑ p : Sym (↥A) (Fintype.card V), P (p.val.map Subtype.val) / (Numbered.divisor (p.val.map Subtype.val):ℝ) =
    ∑ v : V → A,P (Numbered.bag (fun j => (v j).val)) / ((Fintype.card V).factorial:ℝ) := by
  classical
  rw [← Fintype.sum_fiberwise (Numbered.numbers (α:=V) (β:=↥A))]; refine sum_congr rfl fun s _ => ?_
  let T := {v : V→A // Numbered.numbers v = s}
  have h (i : T) : Numbered.bag (fun j => (i.val j).val) = s.val.map Subtype.val := by
    rw [← congr_arg Subtype.val i.property]; exact (Multiset.map_map ..).symm
  simp_rw [h, sum_const,card_univ,nsmul_eq_mul]
  have he := Numbered.pack_count (α:=V) s
  have hf : (Fintype.card T:ℝ) * (Numbered.divisor s.val:ℝ) = (Fintype.card V).factorial := by exact_mod_cast (show Fintype.card T * Numbered.divisor s.val = _ by convert! he using 2; unfold T; congr 1; apply Subsingleton.elim)
  have hp : (0:ℝ) < (Fintype.card V).factorial := by positivity
  rw [divisor_map (m:=s.val) Subtype.val_injective]
  have := Numbered.divisor_pos s.val; field_simp; linear_combination P (s.val.map Subtype.val) * -hf

/-- Passing a summability and size estimate through numbering with replacement.
Not treating the multiset as a set. Empty paid term must vanish. -/
theorem gather {P : Multiset α → ℝ} {c : ℝ} (hp : ∀ i,0 ≤ P i) (h0 : P 0 = 0)
    (h : SumBudget (fun u : Tuple α => P (Numbered.bag u.2) / ((u.1+1).factorial:ℝ)) c) :
    SumBudget (fun m => P m / (Numbered.divisor m:ℝ)) c := by
  let g (m : Multiset α) := P m / (Numbered.divisor m:ℝ)
  have hg i : 0 ≤ g i := div_nonneg (hp i) (by positivity)
  apply Budget.certify hg; intro t
  let s := t.erase 0
  let A := s.biUnion Multiset.toFinset
  let V (i : ℕ) := Fin (i+1)
  let B (i : ℕ) := Sym (↥A) (Fintype.card (V i))
  let S := s.image (fun m => m.card-1)
  let T := S.sigma (fun i => (univ:Finset (B i)))
  let read (i : Σ i, B i) := i.2.val.map (Subtype.val : A → α)
  let q (i : Tuple (↥A)) : Tuple α := ⟨i.1,fun j => (i.2 j).val⟩
  have hq : Injective q := by
    rintro ⟨i,f⟩ ⟨j,e⟩ he; obtain rfl := congr_arg Sigma.fst he
    congr 1; ext j; exact congr_fun (eq_of_heq (Sigma.mk.inj he).2) j
  have he : s ⊆ T.image read := by
    intro i hi
    have hk := (mem_erase.mp hi).2
    have hl := ne_of_mem_erase hi
    let k := i.card-1
    have hm : i.card=Fintype.card (V k) := by
      unfold V; rw [Fintype.card_fin]; have := Multiset.card_pos.mpr hl; omega
    let f (a : {j // j ∈ i}) : A := ⟨a.val,mem_biUnion.mpr ⟨i,hi,Multiset.mem_toFinset.mpr a.property⟩⟩
    let b : B k := ⟨i.attach.map f, (by rw [Multiset.card_map,Multiset.card_attach]; exact hm)⟩
    exact mem_image.mpr ⟨⟨k,b⟩,mem_sigma.mpr ⟨mem_image_of_mem _ hi,mem_univ _⟩, (Multiset.map_map ..).trans (Multiset.attach_map_val _)⟩
  calc
    _ = ∑ i∈s,g i := (sum_subset (erase_subset _ _) (fun i hi hh => by
      obtain rfl := not_ne_iff.mp (mt (fun h => mem_erase.mpr ⟨h,hi⟩) hh); simp [g,h0])).symm
    _ ≤ ∑ j∈T.image read,g j := sum_le_sum_of_subset_of_nonneg he (fun _ _ _ => hg _)
    _ ≤ ∑ j∈T,g (read j) := sum_image_le_of_nonneg fun _ _ => hg _
    _ = ∑ j∈S, ∑ v : V j → A,P (Numbered.bag (fun i => (v i).val)) / ((j+1).factorial:ℝ) := by
      rw [sum_sigma]; exact sum_congr rfl fun j _ => by
        have he := expand_sum P A (V j)
        conv at he => rhs; arg 2; intro v; rw [show Fintype.card (V j) = j+1 from Fintype.card_fin _]
        convert he using 2; ext; simp
    _ ≤ _ := by
      rw [sum_sigma']; refine (le_of_eq ?_).trans (Budget.cap h ((S.sigma fun i => (univ:Finset (V i → A))).image q))
      rw [sum_image hq.injOn]

variable {a b γ : ℝ}

private lemma connected (u : Tuple α) (X : α→Support n) (hs : Ac.Spark X (Numbered.bag u.2).toFinset) (hn : ∀ i, (X (u.2 i)).Nonempty) :
    (overlap X u.2).Connected := by
  simp only [Numbered.bag,Multiset.toFinset_map,show (univ : Finset (Fin (u.1+1))).val.toFinset = univ by ext; simp] at hs
  have he i := mem_image_of_mem u.2 (mem_univ i)
  let H := overlap X u.2
  refine ⟨fun i j => ?_⟩
  have hx a (p : Ac.chain X (univ.image u.2) (u.2 i) a) (b) (hb : u.2 b=a) (hw : (X a).Nonempty) : H.Reachable i b := by
    induction p generalizing b with
    | refl =>
      by_cases h : i=b; subst b; exact SimpleGraph.Reachable.refl i
      obtain ⟨x,hx⟩ := hw; exact (show H.Adj i b from ⟨h,x,hx,hb ▸ hx⟩).reachable
    | @tail c v _ hc IH =>
      obtain ⟨x,hc',hx⟩ := hc.2.2
      obtain ⟨d,_,hd⟩ := mem_image.mp hc.1
      by_cases h : d=b
      · exact h ▸ IH d hd ⟨x,hc'⟩
      exact (IH _ hd ⟨x,hc'⟩).trans (show H.Adj d b from ⟨h,x,hd ▸ hc',hb ▸ hx⟩).reachable
  have h' := hs.2 (u.2 i) (he i) (u.2 j) (he j)
  exact hx _ h' j rfl (hn j)


def collect (X : α → Finset β) (u : Multiset α) := u.toFinset.biUnion X

def paid (f : α → ℝ) (u : Multiset α) := (u.map f).prod / (Numbered.divisor u:ℝ)

def mesh (X : α → Support n) (u : Multiset α) := Ac.Spark X u.toFinset ∧ ∀ i ∈ u, (X i).Nonempty

lemma paid_nonneg {f : α → ℝ} (hf : ∀ i,0≤f i) (u : Multiset α) : 0≤paid f u := by
  rw [paid,prod_multiset_map_count]; exact div_nonneg (prod_nonneg fun i _ => pow_nonneg (hf i) _) (Nat.cast_nonneg _)

theorem connected_budget (X : α → Support n) (M : ℕ) (ok : α → Prop) {f : α → ℝ} (hb : 0≤b) (hγ : 0 ≤ γ)
    (hZ : 8*((M+M+1:ℕ):ℝ)^4*γ ≤ 1) (ha : 0 ≤ a) (hf : ∀ i,0 ≤ f i) (hk : Ac.Hit X M f (a+1) γ)
    (h : SumBudget (fun i => if ok i then Real.exp ((a+1)*coverNumber M (X i)) * f i else 0) b) :
    SumBudget (fun u : Multiset α => if mesh X u ∧ ∃ i∈u, ok i then
        Real.exp (a*coverNumber M (collect X u))*paid f u else 0) (2*b) := by
  let mesh' (u : Tuple α) := mesh X (Numbered.bag u.2)
  let c (u : Tuple α) : ℝ := if mesh' u then 1 else 0
  have he u : 0 ≤ c u ∧ ∀ r, c u ≤ (spans (overlap X u.2) r).card := by
    unfold c; split
    next h =>
      refine ⟨zero_le_one,fun r => Nat.one_le_cast.mpr (card_pos.mpr ?_)⟩
      obtain ⟨f,hf⟩ := hasTrunk _ (connected _ X h.1 (fun i => h.2 (u.2 i) (Multiset.mem_map.mpr ⟨_,mem_val.mpr (mem_univ _),rfl⟩))) r
      exact ⟨f, by simpa [spans] using hf⟩
    exact ⟨le_rfl,fun r => Nat.cast_nonneg _⟩
  let P (u : Multiset α) := if mesh X u ∧ ∃ i∈u,ok i then Real.exp (a*coverNumber M (collect X u))*(u.map f).prod else 0
  have hp i : 0 ≤ P i := by
    unfold P; split; rw [prod_multiset_map_count]; exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun j _ => pow_nonneg (hf j) _); rfl
  have h0 : P 0=0 := by simp [P]
  have hP : SumBudget (fun u : Tuple α => P (Numbered.bag u.2) / ((u.1+1).factorial:ℝ)) (2*b) := by
    convert! repeated X M f c ok b γ a hb hγ hZ ha hf he hk h using 2 with u
    have ht : (∃ i∈Numbered.bag u.2, ok i) ↔ ∃ i,ok (u.2 i) := by simp only [Numbered.bag,Multiset.mem_map,mem_val,mem_univ,true_and]; grind
    dsimp only [P]; simp only [ht,worth,c,mesh']; simp only [Numbered.bag,Multiset.map_map]; split_ifs <;> try simp only [one_div,zero_div,zero_mul,mul_zero]
    next hm ho =>
      have hu : collect X (univ.val.map u.2) = numbered X u := by ext; simp only [collect,numbered,mem_biUnion,Multiset.mem_toFinset,Multiset.mem_map,mem_univ,mem_val,true_and]; grind
      rw [hu,div_eq_mul_inv]; change (_*(∏ i,f (u.2 i)))*_=_ ; ring
    all_goals tauto
  convert! gather hp h0 hP using 2 with i; dsimp only [P,paid]; split_ifs <;> ring

structure Pool (names : α → Finset V) (X : α → Support n) (M : ℕ) (a : ℝ) (f : α→ℝ) (b γ : ℝ) : Prop where
  positive i : 0 ≤ f i
  hit : Ac.Hit X M f a γ
  root : Rooted names X M a f b

/-- Sufficient majorant per output address (e.g. after restoration of the
forced exclusions). `old` ranges over primitives; target can be any set of
outputs, including retained labels with zero majorant. `g` below should pay
the *actual* absolute size you need, through the forced divisor / derivatives
as appropriate; every needed local size bound about the underlying objects
is additional. Doesn't itself require another symmetry or calculate outputs.
-/
structure Display (names : α → Finset V) (X : α → Support n) (s : ι → Finset V) (Y : ι → Support n)
    (f : α → ℝ) (g : ι → ℝ) (q : ℝ) : Prop where
  report : ∃ m : ι → Multiset α, Set.InjOn m {i | 0<g i} ∧ ∀ i,0<g i → mesh X (m i) ∧ Y i ⊆ collect X (m i) ∧
      s i = collect names (m i) ∧ ((m i).toFinset : Set α).PairwiseDisjoint names ∧
      (∀ j, 2 ≤ (m i).count j → names j = ∅) ∧ g i ≤ q * paid f (m i)

lemma duty_paid {m : Multiset α} {names : α→Finset V} (h : (m.toFinset : Set α).PairwiseDisjoint names)
    (he : ∀ j, 2 ≤ m.count j → names j = ∅) (w : V→ℝ) (f : α→ℝ) :
    duty w (collect names m)*paid f m = paid (fun j => duty w (names j)*f j) m := by
  rw [duty,collect,prod_biUnion h]
  have he' i (hi : i∈m.toFinset) : duty w (names i) = (duty w (names i))^m.count i := by
    have ht := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hi)
    by_cases h : m.count i = 1
    · simp [h]
    rw [he i (by omega)]; simp [duty]
  change (∏ i∈m.toFinset,duty w (names i))*_=_
  rw [paid,←mul_div_assoc,paid,prod_multiset_map_count,prod_multiset_map_count, prod_congr rfl he',←prod_mul_distrib]
  simp_rw [mul_pow]

theorem Pool.resold {X : α→Support n} {t : α→Finset V} {M : ℕ} {s : ι → Finset V} {Y : ι → Support n}
    {u : V → ℝ} {f : α → ℝ} {g : ι → ℝ} {q : ℝ} (h : Pool t X M (a+1) (fun i => duty u (t i)*f i) b γ)
    (hp : Display t X s Y f g q) (hu : ∀ i,0 ≤ u i) (hg : ∀ i,0 ≤ g i) (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hZ : 8*((M+M+1:ℕ):ℝ)^4*γ ≤ 1) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    Pool s Y M a (fun i => duty u (s i)*g i) (q*(2*b)) (q*(2*γ)) := by
  let F i := duty u (s i)*g i
  let f' i := duty u (t i)*f i
  have hF i : 0 ≤ F i := mul_nonneg (prod_nonneg fun _ _ => hu _) (hg _)
  obtain ⟨m,hi,hm⟩ := hp.report
  have H (ok : ι → Prop) (okk : α → Prop) {K : ℝ} (hK : 0 ≤ K)
      (hk : SumBudget (fun i => if okk i then Real.exp ((a+1)*coverNumber M (X i)) * f' i else 0) K)
      (hr : ∀ i,0<g i → ok i → ∃ j∈m i,okk j) : SumBudget (fun i => if ok i then Real.exp (a*coverNumber M (Y i))*F i else 0) (q*(2*K)) := by
    refine Budget.pull_le (p:=fun i => 0 < g i ∧ ok i) (Budget.scale (connected_budget X M okk hK hγ hZ ha h.positive h.hit hk) hq) (fun i => ?_)
      (fun i => ?_) (hi.mono fun i hi => hi.1) (fun i ⟨hg',hok⟩ => ?_)
    · split <;> first | exact mul_nonneg (Real.exp_pos _).le (hF i) | exact le_rfl
    · dsimp; split
      next he => exact fun ht => ⟨(hg i).lt_of_ne (Ne.symm (right_ne_zero_of_mul (right_ne_zero_of_mul ht))),he⟩
      simp
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hm i hg'
    rw [if_pos hok,if_pos ⟨h1,hr i hg' hok⟩]
    apply (mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Corona.cover_mono h2 M)) ha))
      (mul_le_mul_of_nonneg_left h6 (show 0 ≤ duty u (s i) from prod_nonneg fun v _ => hu _)) (hF i) (Real.exp_pos _).le).trans_eq
    rw [h3, mul_left_comm (duty u _),duty_paid h4 h5, mul_left_comm]
  refine ⟨hF,fun x => ?_, fun v => ?_⟩
  · simpa [mul_comm,F] using! H (x∈Y ·) (x∈X ·) hγ (by simpa [mul_comm,f'] using h.hit x) fun i hi hx => by
      simpa [collect] using ((hm i hi).2.1 hx)
  simpa [F] using! H (v∈s ·) (v∈t ·) hb (by convert! h.root v using 2; split_ifs <;> rfl) fun i hi hv => by
    obtain ⟨z,hz,hh⟩ := mem_biUnion.mp ((hm i hi).2.2.1 ▸ hv : v∈collect t (m i)); exact ⟨z,Multiset.mem_toFinset.mp hz,hh⟩

end YM.Extra.Multi.Merger
