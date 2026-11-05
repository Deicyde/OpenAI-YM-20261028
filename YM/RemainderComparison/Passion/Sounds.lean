import YM.RemainderComparison.Passion.Scent
/-!
After c.Ap orientation: rooted adjusted logs retain root *unions incl old
connectors*. Both field-mask evaluations (placing literal Section headers or
expanding mask to all carriers) charged. Every induced commission survives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
open SeatD
structure Plane (G:Gauge)(n:Side)(θ:Type) where
   visor : θ→ SeatD G n
   exam : θ→Prop
variable (V: Plane G n θ)
variable (X:Hol G)
structure AxisG (c:ℝ)(t:ℕ)(d:ℝ) : Prop where
   growth i : V.exam i → Local.Readable X (V.visor i).sectionQ p n c
   stencil i : V.exam i → Local.atomRadius (V.visor i).sectionQ ≤ t
   atom i: V.exam i → Local.atomPrice X (V.visor i).basis c ≤ d
   warm : 1 ≤ d
structure Placed (D:ι→Finset θ): Prop where
   legs i j : j∈ D i→ (V.visor j).origin∈ R i
-- station notes. D may be inferred by b but dependent κ. test names roots occupy crane budget.
variable (M:MaskType)(b:Roll T R Z D)
local notation "W₀" => mapWord D
local notation "T'" => W₀ (T.marks b.val.val)
local notation "Y₁" => T.halls b.val.val
local notation "H₁" => Passion.stem T R Z b
inductive BoardState (G:Gauge)(n:Side)(θ:Type)
 | measuring (x:θ)
 | dark
-- use Option
def Ra : Option θ := if h : ∃ i:θ,mapWord D (T.marks b.val.val)={i} ∧ V.exam i then some (Classical.choose h) else none
local notation "WΔ"=> T.marks b.val.val
omit [∀ i,NormedSpace ℝ (Q i)] in
lemma charted (i:θ) : Ra T R Z V b=some i↔ mapWord D (WΔ)={i} ∧ V.exam i:=by
    unfold Ra; split; next h=>
       rw [Option.some.injEq]; constructor; intro h'; exact h' ▸ h.choose_spec
       intro hx; simpa using (h.choose_spec.1.symm.trans hx.1)
    next h=> exact iff_of_false (by simp) (fun hp=> h ⟨_, hp⟩)
-- Reading when measurement chosen
variable (α: Audited Q)(i:θ)
local notation "S₁" => V.visor i
set_option quotPrecheck false
local notation "Y"=> Local.joint (V.visor i).sectionQ (V.visor i).origin Y₁
local notation "F₁" => Y

def PairAt := if T.total b.val.val then SeatD.pure S₁ ((Passion.stem T R Z b α) 1) else SeatD.sector p S₁ X Y₁ (Passion.stem T R Z b α)
local notation "Lφ" => PairAt T p R Z V X b
local notation "p'"=> p.threshold
-- wet Input.Photo if slot.Not.Symbol.Use active.S.Co.Core.
variable {σ v:ℝ}
variable (h:Precepts T p R Z D σ v) (hv:Ra T R Z V b=some i) {w d:ℝ}{t:ℕ}
variable (hx: AxisG p V X w t d) (he:Placed R V D)
local notation "N'" => T.wet p α b.val.val
include hv hx h
lemma pantry (U:Config G n)(hp:Healthy p.threshold Y U): N' U= SeatD.sharp p S₁ Y₁ M (Lφ α i) U:=by
    have hz := (charted T R Z V b i).1 hv; have ht:=hx.growth i hz.2
    unfold PairAt; split_ifs with hr
    · rw [SeatD.pure_identity,Passion.absolute T p R Z b h α hr]; have he:= (h.funds.grants.choose_spec.2.1 _ b.val.prop).1.stall; unfold Manor.wet; rw [if_pos hr,he _ hr U]
    rw [masked_sound T p R Z b h α hr]; exact dayAgree p S₁ X Y₁ M U _ ht (Passion.holds T p R Z b h α) hp
omit h hx
include he
omit [∀ i,NormedSpace ℝ (Q i)] in
lemma sits : (V.visor i).origin ∈ Y₁:=by
    have ht:= (charted T R Z V b i).1 hv; have hu : i∈ mapWord D (WΔ):=by rw [ht.1]; exact Multiset.mem_singleton_self _
    obtain ⟨j,hj,H⟩:= Multiset.mem_bind.mp hu; exact b.prop.2 j hj (he.legs j i H)
omit [∀ i,NormedSpace ℝ (Q i)] in
lemma nested : Y₁⊆ Y∧ (V.visor i).origin∈Y₁:=⟨Finset.subset_union_left,sits T R Z V b i hv he⟩
omit he
include h hx
lemma opal : Core p S₁ X Y₁ M (Lφ α i):=by
   unfold PairAt; split_ifs; next he=> exact snowy ..
   next he=> exact sector_core p S₁ X Y₁ M _ (hx.growth i ((charted T R Z V b i).1 hv).2) (Passion.holds T p R Z b h α)
lemma beams : SeatD.Depends S₁ ( (W₀ WΔ).toFinset) (fun a=> Lφ a i):=by
   unfold PairAt; split_ifs; next he=> exact SeatD.limber _ (Solos.growth _ _ _)
   next he=> exact SeatD.wistful p S₁ X Y₁ _ (hx.growth i ((charted T R Z V b i).1 hv).2) (fun u=>Passion.holds T p R Z b h u) (fun x=>Solos.growth _ _ _)
-- weight stage fees
lemma points {d':ℝ}(hp:p.supBounds (V.visor i).origin Y₁ (H₁ α) d') : Palette p S₁ Y₁ M (Lφ α i) (V.visor i).origin (d*d'):=by
   unfold PairAt; have hs:=hp.1; split_ifs with he
   · apply pale; apply le_trans (hp.2 1 (by
       unfold Healthy; rw [PhysicalNext.Repeat.Boulevard.smoky (P:=p) (show (1:Config G n) ∈ PhysicalNext.Repeat.Boulevard.sunny p from (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using p.threshold_pos))]; simp) [] (Nat.zero_le _) (by simp)); exact le_mul_of_one_le_left hs hx.warm
   have he':= ((charted T R Z V b i).1 hv).2
   obtain ⟨ha,hp,hQ⟩:= SeatD.sold p S₁ X Y₁ M _ (hx.growth i he') (Passion.holds T p R Z b h α) hp
   have hk:= mul_le_mul_of_nonneg_right (hx.atom i he') hs; exact ⟨ha.trans hk, VerifiedReset.sup_le hp hk,VerifiedReset.sup_le hQ hk⟩
end YM.RemainderComparison.Passion
