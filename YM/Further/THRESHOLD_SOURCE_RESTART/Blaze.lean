import YM.Further.THRESHOLD_SOURCE_RESTART.Baked
/-!
# Exact coverage with the new and old K masks at k

Include the old support-disjointness checks (not the inflated versions),
flag equality and compulsory-list exactness. On a fixed torus,
with ALL winding labels already retained. The `balance` proof will use the
hasSum version for regrouping.
Proof method extends `Push.CORRECTED_COLUMNS` `.Invited`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Sluice.Menu
open Function Set Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Work.H03 WilsonStartup Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {α : Type} {n : Side} {H : Rep G n} {q : BudgetPoint} (L : Menu H q α)

def alloted (B : Finset L.Record) := B.biUnion Subtype.val
def Mass (B : Finset L.Record) (U : Config G n) := (B : Set L.Record).PairwiseDisjoint (fun i => L.limit i.val) ∧
    B.biUnion (fun i => L.inv i.val)=flags q.threshold U

lemma posters (B : Finset L.Record) : L.inv (L.alloted B)=B.biUnion (fun i=>L.inv i.val) := by
  ext x; simp only [inv,paint,alloted, Finset.mem_biUnion, Finset.mem_toLeft,Finset.mem_toRight]; grind
lemma quota (B : Finset L.Record) : (L.alloted B).toLeft=B.biUnion (fun i=>i.val.toLeft) := by
  ext; simp only [alloted,Finset.mem_biUnion,Finset.mem_toLeft]

variable {U : Config G n} {B : Finset L.Record}
lemma all_of_it (h : L.Mass B U) (hh : ∀ i∈B,L.Ready i U) : L.paint (L.alloted B)=listAll q U := by
  ext i; constructor
  · intro he; obtain ⟨b,hb,ht⟩ := mem_biUnion.mp (mem_toRight.mp (mem_toLeft.mp he))
    exact (hh b hb).1 (mem_toLeft.mpr (mem_toRight.mpr ht))
  intro he; have hp : i.native ∈ flags q.threshold U := claim_all q U ▸ Finset.mem_biUnion.mpr ⟨i,he,i.native_mem⟩
  rw [← h.2] at hp; obtain ⟨b,hb,hm⟩ := mem_biUnion.mp hp
  have hx : ¬ Disjoint i.skin (L.inv b.val) := not_disjoint_iff.mpr ⟨_,i.native_mem,hm⟩
  have ht := (hh b hb).2.1 _ he hx
  exact mem_toLeft.mpr (mem_toRight.mpr (mem_biUnion.mpr ⟨b,hb,mem_toRight.mp (mem_toLeft.mp ht)⟩))
lemma old_survives (h : L.Mass B U) (hh : ∀ i∈B,L.Ready i U) : H.activities.admissible H.p U (L.alloted B).toLeft := by
  rw [L.quota]; constructor
  · intro i hi j hj e
    obtain ⟨b,hb,hI⟩ := mem_biUnion.mp (show _∈_ from hi); obtain ⟨r,hr,hJ⟩ := mem_biUnion.mp (show _∈_ from hj)
    rcases eq_or_ne b r with hp|hp
    · subst r; exact b.property.2.2 hI hJ e
    exact disjoint_left.mpr fun x hx hz => disjoint_left.mp (h.1 hb hr hp) (L.halo_charge _ _ hI (Halos.enters hx))
      (L.halo_charge _ _ hJ (Halos.enters hz))
  ext x; constructor
  · intro he; obtain ⟨j,hj,ht⟩ := mem_biUnion.mp he; obtain ⟨b,hb,hj⟩ := mem_biUnion.mp hj
    have he := (hh b hb).2.2.1 _ hj
    exact (Finset.mem_inter.mp (he.1.symm ▸ ht)).2
  intro he
  have hp : x ∈ flags q.threshold U := by
    obtain ⟨P,hP,h'⟩ := (flags_spec ..).mp he; exact (flags_spec ..).mpr ⟨P,hP,L.shrinks.trans_lt h'⟩
  rw [← h.2] at hp; obtain ⟨b,hb,hx⟩ := mem_biUnion.mp hp
  obtain ⟨i,hi,h⟩ := mem_biUnion.mp ((hh b hb).2.2.2 (Finset.mem_inter.mpr ⟨hx,he⟩))
  exact mem_biUnion.mpr ⟨i,mem_biUnion.mpr ⟨b,hb,hi⟩,h⟩

-- conversely using every nonzero glow. Old K not tested nonzero! Need
-- selection even for zero old vacuum terms.
theorem takeoff {t : Finset ℕ} {A : Finset α} (h : H.activities.admissible H.p U t) (h' : ∀ i∈t,permits H i U)
    (he : ∀ i∈A,L.glow (.inr (.inr i)) U≠0) : ∃ B : Finset L.Record, L.Mass B U ∧
    (∀ i∈B,(L.sole i).eligible q.threshold U) ∧ L.alloted B=t.disjSum ((listAll q U).disjSum A) := by
  let X := t.disjSum ((listAll q U).disjSum A); let Y := Ac.Parts L.zone X
  have hx : L.paint X=listAll q U := by simp [paint,X]
  have hy : L.inv X=flags q.threshold U := by unfold inv; rw [hx,claim_all]
  have hY (p : ↥Y) : L.Fuel p.val := by
    have hp := Ac.lives L.zone X p.property
    refine ⟨hp.2,?_,fun i hi j hj e => h.1 ?_ ?_ e⟩
    · obtain ⟨i,hi⟩ := hp.2.1
      have hw {x} (he : x∈L.zone i) (H : x∈flags q.threshold U) : (L.paint p.val).Nonempty := by
        obtain ⟨j,hj,hV⟩ := mem_biUnion.mp (show x∈L.inv X from hy ▸ H)
        have hQ := mem_toRight.mp (mem_toLeft.mp hj)
        have hr : Sum.inr (Sum.inl j)∈Ac.burst L.zone X i := (Ac.bright ..).mpr
          ⟨hQ,Relation.ReflTransGen.single ⟨hp.1 hi,hQ,x,he,watches q _ (Halos.enters hV)⟩⟩
        rw [Ac.contains L.zone p.property i hi] at hr
        exact ⟨j,mem_toLeft.mpr (mem_toRight.mpr hr)⟩
      rcases i with i|i|i
      · obtain ⟨x,hx⟩ := (H.activities.forced i).inventory_ne
        have ht : i∈t := inl_mem_disjSum.mp (hp.1 hi)
        have he := (h' i ht).1
        have hi : x∈flags H.p.threshold U := (Finset.mem_inter.mp (he.symm ▸ hx)).2
        obtain ⟨P,hP,h⟩ := (flags_spec ..).mp hi
        exact hw (Halos.enters ((H.activities.forced i).inventory_sup hx)) ((flags_spec ..).mpr ⟨P,hP,L.shrinks.trans_lt h⟩)
      · exact ⟨i,mem_toLeft.mpr (mem_toRight.mpr hi)⟩
      have hv := he i (inr_mem_disjSum.mp (inr_mem_disjSum.mp (hp.1 hi)))
      have hM : L.more.leaf i U ≠ 0 := fun H => hv (by simp [glow,H])
      obtain ⟨x,hb,hh⟩ := Finset.not_disjoint_iff.mp (L.more.needy _ _ hM); exact hw hb hh
    · exact inl_mem_disjSum.mp (hp.1 (mem_toLeft.mp hi))
    exact inl_mem_disjSum.mp (hp.1 (mem_toLeft.mp hj))
  let f (p : ↥Y) : L.Record := ⟨p.val,hY p⟩
  let B := Finset.univ.image f
  have hp : L.alloted B=X := by
    apply Eq.trans _ (show Y.biUnion id=X from Ac.reconstruct L.zone X)
    ext y; unfold alloted B; rw [Finset.mem_biUnion,Finset.mem_biUnion]; constructor
    · rintro ⟨i,hi,h⟩; obtain ⟨p,-,rfl⟩ := mem_image.mp hi; exact ⟨p.val,p.property,h⟩
    rintro ⟨p,hp,h⟩; exact ⟨f ⟨p,hp⟩,mem_image_of_mem f (mem_univ (⟨p,hp⟩ : ↥Y)),h⟩
  have hB : L.Mass B U := by
    refine ⟨fun i hi j hj e => ?_,(L.posters B).symm.trans ((congr_arg _ hp).trans hy)⟩
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hi; obtain ⟨s,hs,rfl⟩ := mem_image.mp hj
    exact Ac.separate _ _ p.property s.property (fun he => e (Subtype.ext he))
  refine ⟨B,hB,fun i hi => ?_,hp⟩
  have ht i (hi : i∈B) : L.paint i.val ⊆ listAll q U := by
    intro j hj
    apply inl_mem_disjSum.mp (inr_mem_disjSum.mp (show Sum.inr (Sum.inl j) ∈ X from
      hp ▸ mem_biUnion.mpr ⟨i,hi,mem_toRight.mp (mem_toLeft.mp hj)⟩))
  have hq j (hj : j∈B) (x) (hm : x∈L.limit j.val) (hM : x∈L.limit i.val) : j=i := by_contra
    fun e => disjoint_left.mp (hB.1 hj hi e) hm hM
  constructor
  · change L.limit i.val ∩ flags q.threshold U = L.inv i.val
    ext x; rw [←hB.2,Finset.mem_inter]; constructor
    · rintro ⟨hx,hx'⟩; obtain ⟨b,hb,hh⟩ := mem_biUnion.mp hx'
      have hk := hq b hb x (L.has_supp _ hh) hx
      subst b; exact hh
    intro h; exact ⟨L.has_supp i.val h, mem_biUnion.mpr ⟨i,hi,h⟩⟩
  change L.Ready i U
  refine ⟨ht i hi,fun j hj he => ?_, fun j hj => h' j (inl_mem_disjSum.mp (show _∈X from
    hp ▸ Finset.mem_biUnion.mpr ⟨i,hi,mem_toLeft.mp hj⟩)),?_⟩
  · obtain ⟨x,hx,hx'⟩ := not_disjoint_iff.mp he
    have hh : j ∈ L.paint (L.alloted B) := by rw [hp,show L.paint X=listAll q U from ‹_›]; exact hj
    obtain ⟨b,hb,hh⟩ := mem_biUnion.mp (mem_toRight.mp (mem_toLeft.mp hh))
    have hQ := hq b hb x (mem_biUnion.mpr ⟨_,hh,watches q j (Halos.enters hx)⟩) (L.has_supp _ hx')
    subst b; exact mem_toLeft.mpr (mem_toRight.mpr hh)
  intro x hx; obtain ⟨hv,hx⟩ := mem_inter.mp hx
  rw [← h.2] at hx; obtain ⟨p,hp',hP⟩ := mem_biUnion.mp hx
  have hh : Sum.inl p ∈ L.alloted B := by rw [hp]; exact inl_mem_disjSum.mpr hp'
  obtain ⟨j,hj,Hj⟩ := mem_biUnion.mp hh
  have h' := hq j hj x (L.halo_charge _ _ (mem_toLeft.mpr Hj) (Halos.enters ((H.activities.forced p).inventory_sup hP))) (L.has_supp _ hv)
  subst j; exact mem_biUnion.mpr ⟨p,mem_toLeft.mpr Hj,hP⟩
end YM.Further.ThresholdSourceRestart.Sluice.Menu
