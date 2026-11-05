import YM.RemainderComparison.Passion.Pigment
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
variable {σ b c e :ℝ} (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι) (V:Plane G n θ) (X:Hol G)
variable (M:SeatD.MaskType)(i:Roll T R Z D)
local notation "W₀" => mapWord D
local notation "T₀"=> T.marks i.val.val
local notation "P"=> T.halls i.val.val
local notation "v₀"=> p.threshold
local notation "Ra₀"=> Ra T R Z V i
local notation "P₁"=> SeatD.PairD
set_option quotPrecheck false
open SeatD
-- retain an explicit MODE which interprets canonical only once. grants on both; architecture for Θ joint proof.Hit
variable (a:Audited Q)
def area : Support n:= match (Ra T R Z V i) with
 | none=> T.halls i.val.val
 | some z=> Local.joint (V.visor z).sectionQ (V.visor z).origin (T.halls i.val.val)
local notation "A"=> area T R Z V i
local notation "α"=> Audited Q
local notation "L'"=> T.wet p
local notation "Q₁" => (Passion.stem T R Z i)

def amount : Config G n→ℝ:= match Ra₀ with
 | none=> if T.total i.val.val then Passion.stem T R Z i a else masked v₀ P (Passion.stem T R Z i a) -- use after multilinear repair
 | some z=> SeatD.sharp p (V.visor z) (T.halls i.val.val) M (Passion.PairAt T p R Z V X i a z)
local notation "q"=> amount T p R Z V X M i

def leakage := T.wet p a i.val.val-q a
local notation "h₂"=> leakage T p R Z V X M i
variable (h:Precepts T p R Z D σ b) {t:ℕ} (hr: Placed R V D)(he:AxisG p V X c t e)
open PhysicalNext.Repeat Trio
omit [∀ i,NormedSpace ℝ (Q i)] in
lemma lanes : P ⊆ A:=by unfold area; cases Ra T R Z V i; exact Finset.Subset.rfl; exact Finset.subset_union_left
omit [∀ i,NormedSpace ℝ (Q i)] in
lemma rooted : legitim T R i.val.val ∧ ∀ z∈ T₀,R z⊆ A:= ⟨i.prop.2,fun z hz=> Finset.Subset.trans (i.prop.2 z hz) (lanes T R Z V i)⟩
include h he
lemma heart : Trio.Tidy p A (q a) :=by
    unfold area amount; cases hp: Ra T R Z V i with
    | none=>
        split_ifs with he
        · rw [show Q₁ a=(fun _=> T.solvent a i.val.val 1) from funext fun U=> Passion.absolute T p R Z i h a he U]; exact Trio.tidy_const p _
        exact Trio.tidy_mask p (Passion.holds T p R Z i h a) Finset.Subset.rfl
    | some z=> exact SeatD.Core.note p _ X _ _ (Passion.opal T p R Z V X M i a z h hp he)
lemma literal (U:Config G n)(hp:Healthy v₀ A U): leakage T p R Z V X M i a U=0:=by
    unfold leakage; dsimp only [Pi.sub_apply]; unfold area at hp; unfold amount; cases hT:Ra₀ with
    | none=>
        split_ifs with hg
        · dsimp only; rw [Passion.absolute T p R Z i h a hg U]; unfold Manor.wet; rw [if_pos hg,(h.funds.grants.choose_spec.2.1 _ i.val.prop|>.1.stall a hg U),sub_self]
        dsimp only;         rw [masked_sound T p R Z i h a hg,sub_self]
    | some z=>rw [hT] at hp; exact sub_eq_zero.mpr (pantry T p R Z V X M i a z h hT he U hp)
lemma vocals (U:Config G n) : LinearP ( (mapWord D T₀).toFinset) fun j=> amount T p R Z V X M i j U:=by
    unfold amount; cases hp: Ra₀ with
    | some z => exact SeatD.Depends.era p _ _ M _ (beams T p R Z V X i z h hp he) U
    | none=> split_ifs with hx
             next isTrue=> exact Solos.growth _ _ _
             next isFalse=>
                 by_cases he:Healthy v₀ P U
                 · simp_rw [fun z=> masked_eq _ _ (Q₁ z) U he]; exact Solos.growth _ _ _
                 simp_rw [fun z=> masked_ne _ _ (Q₁ z) U he]; exact LinearP.nil _
lemma scoreLeak (U:Config G n) : LinearP ((mapWord D T₀).toFinset) fun j=> leakage T p R Z V X M i j U :=by
    apply LinearP.wing _ (Passion.vocals T p R Z V X M i h he U)
    exact Solos.migrant D T p h.lineage (fun i hi=> (h.funds.grants.choose_spec.2.1 i hi).1) i.val.val i.val.prop U i.prop.1

lemma nearT : Trio.Tidy p A (leakage T p R Z V X M i a):=by
    apply Trio.tidy_sub p _ (Passion.heart T p R Z V X M i a h he); exact T.tidied _ (h.funds.grants.choose_spec.2.1 _ i.val.prop|>.1) (lanes ..)

-- bound H width.D.Growth enough with selector Height.Summary.Th.Comparable. Mark leakage Tidy
include hr
omit h [∀ i,NormedSpace ℝ (Q i)] in
lemma spans (x:Site n) (hp:x ∈ A): ∃ y∈ P,y∈ halo t {x}:=by
    unfold area at hp; cases hh: Ra₀ with
    | none=>rw [hh] at hp; exact ⟨x,hp,halo_subset t _ (Finset.mem_singleton_self _)⟩
    | some z=>
        rw [hh] at hp; rcases Finset.mem_union.mp hp with hp|hp
        · exact ⟨x,hp,halo_subset t _ (Finset.mem_singleton_self _)⟩
        refine ⟨(V.visor z).origin,sits T R Z V i z hh hr, halo_spec.mpr ⟨x,Finset.mem_singleton_self _,?_⟩⟩
        rw [separation_comm]; exact (SeatD.visits' (V.visor z) x hp).trans (he.stencil z (((charted T R Z V i z).1 hh).2))
omit h [∀ i,NormedSpace ℝ (Q i)] in
lemma boarded : coverNumber p.B A≤ coverNumber p.B P+stems t:=by
    unfold area; cases hh:Ra₀ with
    | none=> exact Nat.le_add_right ..
    | some z=>
        let o:= (V.visor z).origin; let F:=(V.visor z).sectionQ; have hx:= (((charted T R Z V i z).1 hh).2); have hp:o∈ P:= sits T R Z V i z hh hr
        have hk : o∈ F.footprint o:= Finset.mem_image.mpr ⟨0,(he.growth _ hx).sound.anchored,by simp⟩
        apply (Lattice.Corona.meets_sum hp hk p.B).trans; have hℓ:= he.stencil z hx
        apply Nat.add_le_add_left (Local.atomTiles_price _ _ _|>.trans _); unfold Local.atomTiles stems; gcongr
variable (g: Roll T R Z D→ℝ) (hB:∀ i a x, x ∈ T.halls i.val.val → p.supBounds x (T.halls (i:Roll T R Z D).val.val) (Passion.stem T R Z i a) (g i))
local notation "S₁" => traceWeight p (coverNumber p.B A)
include hB
lemma proof (x:Site n)(hp: x∈ A){z:θ}(hv: Ra₀=some z): SeatD.Palette p (V.visor z) P M (PairAt T p R Z V X i a z) x (S₁*(e*g i)) := by
    have hp' : area T R Z V i = Local.joint (V.visor z).sectionQ (V.visor z).origin P:=by unfold area; rw [hv]
    rw [hp'] at hp ⊢; have hx:=sits T R Z V i z hv hr
    exact SeatD.Palette.extend p _ X _ _ (Passion.opal T p R Z V X M i a z h hv he) hx (points T p R Z V X M i a z h hv he (hB i a _ hx)) hp
lemma bracket (U:Config G n) : let c:=S₁*(e*g i);
     ‖amount T p R Z V X M i a U‖≤ 3*c ∧ ‖leakage T p R Z V X M i a U‖≤ 4*c :=by
    intro c'; have hh:=hB i a _ (T.call _); have he_W:= he.warm; have hl:g i≤ c':= (le_mul_of_one_le_left hh.1 he_W).trans (le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans he_W) hh.1) (freight p _)); have h':0≤c':= hh.1.trans hl
    have hm : ‖T.wet p a i.val.val U‖ ≤ g i:=by
        by_cases hi:T.total i.val.val
        · have hk:= h.funds.grants.choose_spec.2.1 _ i.val.prop; unfold Manor.wet; rw [if_pos hi, (hk.1.stall a hi U),← Passion.absolute T p R Z i h a hi 1]; apply hh.2 1 _ [] (List.length_nil ▸ Nat.zero_le _) (by simp)
          exact one_healthy _ _ p.threshold_pos.le -- find
        rw [masked_sound T p R Z i h a hi]; exact AnalyticBridge.CouplingShape.mask_cost hh _
    suffices ht : ‖q a U‖ ≤ _ from ⟨ht,(norm_sub_le ..).trans ((add_le_add (hm.trans hl) ht).trans (by linarith))⟩
    unfold amount; cases hv:Ra₀ with
    | none=>
        split_ifs with he
        · dsimp only; rw [Passion.absolute T p R Z i h a he]; unfold Manor.wet at hm; rw [if_pos he, (h.funds.grants.choose_spec.2.1 _ i.val.prop|>.1).stall a he U] at hm; linarith
        rw [masked_sound T p R Z i h a he] at hm; exact hm.trans (by linarith)
    | some z=>
        apply SeatD.prices; exact proof T p R Z V X M i a h hr he g hB _ ( (lanes T R Z V i) (sits T R Z V i z hv hr)) hv -- order
end YM.RemainderComparison.Passion
