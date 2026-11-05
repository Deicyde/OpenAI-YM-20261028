import YM.Extra.WILSON_STARTUP.Ink

/-! # Exact gas at startup (before H01/H03) -/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Start
open Function Filter RG Wilson Lattice Design Work Ac Padded Ovens Ovens.Pipes
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {b : BudgetPoint} {c : Clip} {β : ℝ}

abbrev extent (n : Side) (i : ℕ) : Support n := (name (Foot n) i).val.1
abbrev inventory (n : Side) (i : ℕ) : Support n := (name (Foot n) i).val.2
abbrev actual (n : Side) (b : BudgetPoint) (i : ℕ) := fixed (Foot n) i ∧ lives b (name (Foot n) i)

def code (b : BudgetPoint) (p : Support n) : ℕ := if h : p.Nonempty then
    index (α:=Foot n) ⟨(region b p,p),h,subset_region b p⟩ else Classical.arbitrary ℕ

def registry (b : BudgetPoint) (D : Support n) := (parts b D).image (code b)

theorem code_props (b : BudgetPoint) (p : Support n) (h : Spark (pad b) p) :
    actual n b (code b p) ∧ extent n (code b p) = region b p ∧ inventory n (code b p) = p := by
  rw [code,dif_pos h.1]; simp [actual,extent,inventory,lives,h]

theorem unique_actual {i j : ℕ} (h : actual n b i) (he : actual n b j) (hf : inventory n i = inventory n j) : i=j := by
  have hi : name (Foot n) i = name (Foot n) j := Subtype.ext (Prod.ext (h.2.2.trans ((congr_arg (region b) hf).trans he.2.2.symm)) hf)
  exact (index_name h.1).symm.trans ((congr_arg index hi).trans (index_name he.1))

theorem admitted_actual {i : ℕ} {U : Config G n} (h : (raw G n c b β).K i U ≠ 0) : actual n b i := by
  change (if fixed (Foot n) i then paid c b (name (Foot n) i) β else (0 : Config G n → ℝ)) U ≠ 0 at h
  split at h <;> rename_i he
  · exact ⟨he,(by_contra fun h' => h (if_neg fun hh => h' hh.1))⟩
  exact (h rfl).elim

theorem active_reconstruct {s : Finset ℕ} {D : Support n}
    (ht : (s : Set ℕ).PairwiseDisjoint (extent n)) (hc : s.biUnion (inventory n) = D) (he : ∀ i∈s, actual n b i) : s = registry b D := by
  have hi {i} (hh : i∈s) := (he i hh).2.2
  let L := s.image (inventory n)
  have hw (i) (h : i∈L) : Spark (pad b) i := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h; exact (he j hj).2.1
  have hu := separates (pad b) L hw (by
    rintro x hx y hy h
    obtain ⟨i,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hb,rfl⟩ := Finset.mem_image.mp hy
    change Disjoint (region b _) (region b _)
    rw [← hi ha, ← hi hb]; exact ht ha hb (ne_of_apply_ne _ h))
  have hL : L.biUnion id=D := by unfold L; rw [Finset.image_biUnion]; exact hc
  rw [hL] at hu
  rw [registry,parts,hu]; ext i; constructor
  · intro hh
    have hl := Finset.mem_image_of_mem (inventory n) hh
    exact Finset.mem_image.mpr ⟨_,hl, unique_actual (code_props b _ (hw _ hl)).1 (he _ hh) (code_props b _ (hw _ hl)).2.2⟩
  intro hh
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨i,he',hi⟩ := Finset.mem_image.mp hp
  have hf := code_props b p (hw p hp)
  rwa [unique_actual hf.1 (he i he') (hf.2.2.trans hi.symm)]

theorem registered (b : BudgetPoint) (D : Support n) :
    ((registry b D : Finset ℕ) : Set ℕ).PairwiseDisjoint (extent n) ∧ (registry b D).biUnion (inventory n) = D := by
  have he {i} (h : i ∈ parts b D) := code_props b i (Ac.lives (pad b) D h).2
  constructor
  · rintro x hx y hy h
    obtain ⟨i,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j,hb,rfl⟩ := Finset.mem_image.mp hy
    show Disjoint (extent n _) _
    rw [(he ha).2.1,(he hb).2.1]; exact Ac.separate (pad b) D ha hb (ne_of_apply_ne _ h)
  unfold registry; rw [Finset.image_biUnion]; convert Ac.reconstruct (pad b) D using 1
  exact Finset.biUnion_congr rfl fun i hi => (he hi).2.2

theorem issues (U : Config G n) (D : Support n) (hd : D ∈ parts b (flags b.threshold U)) :
    (raw G n c b β).K (code b D) U = Real.exp (-β*charge c b D U) := by
  obtain ⟨⟨h₁,h₂⟩,h₃,h₄⟩ := code_props b D (Ac.lives _ _ hd).2
  rw [raw,pours,payload]; simp only [if_pos h₁, paid, admission,h₂, true_and]
  change (if extent .. ∩ _ = inventory .. then Real.exp (-β*charge c b (inventory n _) U) else 0) = _
  rw [h₃,h₄,coverage b _ hd,if_pos rfl]

theorem code_inj {s : Finset (Support n)} (he : ∀ i∈s, Spark (pad b) i) : Set.InjOn (code b (n:=n)) (s : Set _) := by
  intro i hi j hj h
  exact (code_props b _ (he i hi)).2.2.symm.trans ((congr_arg (inventory n) h).trans (code_props b _ (he j hj)).2.2)

theorem gas_raw (h : Decent c b) (U : Config G n) : (raw G n c b β).gas b U =
    Real.exp (-β * (share * ∑ i : Key n, Key.owed c b i U)) := by
  let D := flags b.threshold U
  unfold Activities.gas
  rw [tsum_eq_single (registry b D)]; swap
  · intro s hs
    unfold Activities.gasOccurrence; split <;> rename_i hh
    · refine of_not_not fun h' => hs (active_reconstruct hh.1 hh.2 ?_)
      intro i hi; exact admitted_actual ((Finset.prod_ne_zero_iff.mp h') i hi)
    rfl
  unfold Activities.gasOccurrence
  have ht : (raw G n c b β).admissible b U (registry b D) := registered b D
  rw [if_pos ht,registry,Finset.prod_image (code_inj (s:=parts b D) (fun i hi => (Ac.lives _ D hi).2))]
  rw [← charge_sum c b h U,Finset.mul_sum, Real.exp_sum]; exact Finset.prod_congr rfl (fun i hi => issues U i hi)

theorem evaluates (h : Decent c b) (U : Config G n) :
    (Bid.Cake (payload c b G n) (dictionary G n) (top G c) c b β).eval U = bare β U := by
  unfold Rep.eval Rep.exponent Bid.Cake; dsimp only
  change Real.exp _ * (raw G n c b β).gas b U = _
  rw [gas_raw h, ← Real.exp_add,bare,zero_mul,zero_sub]
  apply congr_arg Real.exp
  change - _ - (raw G n c b β).additive b U + _ = _
  rw [written_sum, weight]; linarith only [channel_split c b U h.direct β]
end YM.WilsonStartup.Start
