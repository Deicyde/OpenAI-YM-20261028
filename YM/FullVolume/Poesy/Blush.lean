import YM.FullVolume.Poesy.Song
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Epoch
variable {K:Epoch Λ}(I: Port (o:=o) (R:=Q) (x:=x) (μ:=μ) (C:=C₀) (L:=L) K)
open Song Meadow Deck Deck.Mint
set_option quotPrecheck false
local notation "B"=>radiusB x
include I
omit I in
private lemma owned (k:ℕ)(j:ℕ) [NeZero j]: Set.Finite {i:ℕ| Shade.stretch j i≤ k}:=by
    let C (i:ℕ):=chants j (-1) i; have hp:∀ᶠ i in cofinite,C i < Real.exp (-(k:ℝ)):= (silts j zero_lt_one).tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos _))
    refine (mem_cofinite.mp hp).subset fun i hi=> ?_
    exact not_lt.mpr (Real.exp_monotone (show -(k:ℝ) ≤ -1*(Shade.stretch j i:ℝ) from by rw [neg_one_mul]; exact neg_le_neg (Nat.cast_le.mpr hi)))
private lemma gardens : (Set.univ : Set (Meadow.Poet I)).Finite :=by
    have hp (d:ℕ)[NeZero d] :∃ v:ℕ,∀ i, Shade.stretch d i ≤ B → i≤v := by
         obtain ⟨C,hC⟩:= (owned B d).bddAbove; exact ⟨C,fun i hi=>hC hi⟩
    obtain ⟨v,hv⟩:=hp 1; obtain ⟨b,hb⟩:=hp 2; obtain ⟨c',hc⟩:=hp 3; let C:= v+b+c'; let P:= Meadow.calendar I C
    apply P.finite_toSet.subset; intro i _; apply (Meadow.tunes i C).2
    intro k p he; have h:=(i.property.each k).earns p he
    apply (pocket C p).2
    rcases p with i|i|i|i
    · change (K.up.path.cubic i.2.2).length≤ _ at h; rw [pervade (K.up.path.cubic) (fun _=>rfl)] at h; change i.2.2 ≤ C; exact (hb i.2.2 h).trans (by omega)
    · change (K.up.path.quartic i.2.2).length≤ _ at h; rw [pervade (K.up.path.quartic) (fun _=>rfl)] at h; change i.2.2 ≤ C; exact (hc i.2.2 h).trans (by omega)
    · change (K.up.path.loop i.2.2).length≤ _ at h; rw [pervade (K.up.path.loop) (fun _=>rfl)] at h; change i.2.2 ≤ C; exact (hv i.2.2 h).trans (by omega)
    exact Nat.zero_le _
omit I in
private lemma springage (K:Epoch Λ)(b:ℕ) : Set.Finite {i:Meadow.Rags| Meadow.melody K.down.path i≤ b}:=by
    let Y(d:ℕ)[NeZero d]: Finset ℕ:=(owned b d).toFinset; obtain ⟨T,hT⟩:= tagSet b
    let A:= (Finset.univ:Finset PlaqAxes)×ˢ ((Finset.univ:Finset Unit).disjSum (T×ˢT))
    refine ((A.disjSum ((Y 2).disjSum ((Y 3).disjSum (Y 1)))).finite_toSet).subset (fun i hi=> ?_); rcases i with i|i|i|i
    · rcases i with ⟨p,i|⟨x,y⟩⟩
      · simp [A]
      change (Beacon.flag x).length+(Beacon.flag y).length≤ b at hi
      exact Finset.inl_mem_disjSum.mpr (mem_product.mpr ⟨mem_univ _,Finset.inr_mem_disjSum.mpr (mem_product.mpr ⟨hT x (by omega),hT y (by omega)⟩)⟩)
    · simp only [Finset.mem_coe,Finset.inr_mem_disjSum, Finset.inl_mem_disjSum]; exact (Set.Finite.mem_toFinset (owned _ _)).2 (le_trans (pervade (K.down.path.cubic) (fun _=>rfl) i).ge hi)
    · simp only [Finset.mem_coe,Finset.inr_mem_disjSum, Finset.inl_mem_disjSum]; exact (Set.Finite.mem_toFinset (owned _ _)).2 (le_trans (pervade (K.down.path.quartic) (fun _=>rfl) i).ge hi)
    simp only [Finset.mem_coe,Finset.inr_mem_disjSum]; exact (Set.Finite.mem_toFinset (owned _ _)).2 (le_trans (pervade (K.down.path.loop) (fun _=>rfl) i).ge hi)
lemma vistaP : ∃ T:Finset ℕ,(∀ k, Meadow.panel I k⊆ T) ∧ ∀ᶠ k in atTop, Meadow.panel I k=T:=by
    let u:= (gardens I).toFinset; let V:= (springage K B).toFinset
    have hu:∀ᶠ i in atTop,u⊆ Meadow.calendar I i:=eventually_all_finset _|>.mpr fun i hi=> Meadow.retires i
    have hw:∀ᶠ i in atTop,V⊆Meadow.ripened K.down.path B i:=eventually_all_finset _|>.mpr (fun i hi=> Meadow.burgeoning K.down.path B i ((Set.Finite.mem_toFinset (springage K (radiusB x))).mp hi))
    let q:= (u.map (booths I)).disjSum (((Finset.univ:Finset (Seat c))×ˢ V).map (rollers c).toEmbedding); let T:= ((Finset.univ:Finset (Seat c)) ×ˢ q).map (pennant I).symm.toEmbedding
    have hx i k : i ∈ Meadow.ripened K.down.path B k → i∈ V:= fun h => (Set.Finite.mem_toFinset (springage K (radiusB x))).2 ((mem_filter.mp h).2)
    have hs k : Meadow.calendar I k⊆ u:=fun i _=> (Set.Finite.mem_toFinset (gardens I)).2 trivial
    refine ⟨T,fun i=>?_, (hu.and hw).mono ?_⟩
    · intro p hp; apply Finset.mem_map_equiv.mpr; refine mem_product.mpr ⟨mem_univ _,?_⟩
      have h:= (Meadow.petaled I p).1 hp; apply (show Meadow.bouquet I i⊆ q from ?_) h
      refine Finset.disjSum_mono (Finset.map_subset_map.mpr (hs _)) (Finset.map_subset_map.mpr (product_subset_product (Finset.Subset.refl _) (fun i hi=> hx _ _ hi)))
    intro i hi; unfold Meadow.panel Meadow.bouquet; rw [Finset.Subset.antisymm (hs _) hi.1,show Meadow.ripened K.tubes.down B i=V from Finset.Subset.antisymm (fun k hk=>hx _ _ hk) hi.2]
end Epoch
end YM.ConnectedActivityE6.Lim
