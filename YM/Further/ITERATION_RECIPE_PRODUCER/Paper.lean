import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Further.ITERATION_RECIPE_PRODUCER.Menu
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Marks
import YM.Progress.JOINT_CALENDAR.Branches

set_option warningAsError false

/-!
# E §§ppx/Jinit: consuming the Wilson wide birth as a Voice in Histories

On the EXACT selected cutoff rep, despite the Shelf obstruction. Combines
`Song.onTop`'s rotation argument with `Mark.Prepared` (rather than assuming
an output-deviation clock to pass between Histories and Scheduling). Uses
the preselected actual Section of the Authorities, no reconstruction of
its frame/physical polynomial after calibrating. Origin for equation and
step; Readout after via genuine Based demands. Offers for continuity and
`AtomStep` all-sector estimates are **not derived** in this file!
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Motion WilsonStartup
open Bid Precision Next.Scheduling RG.Supply RG.Shoot
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} (S : SectionData F) (H : History G) (N p : ℕ) {A : Hol G}

def voice : Voice F H p N where
  plays := Mark.initialData H S N p 0
  charge v := F.coeffSize (F.core v)
  index := LinearEquiv.refl ℂ _

theorem uses (h : H.Selected) (hS : S.Sound A) (hm : Mark.Prepared H S A N p 0) : OnTop S H N p A (voice S H N p) := by
  let R := H.rep N p N
  let V := voice S H N p
  let t := H.levels.clock.threshold N
  let i (v : F.Coeff) := S.places (F.scaled t⁻¹ v) (0:Site (H.S.side N p))
  let Z (v) := (V.plays v).density 0 S R
  have ha (v U) : Z v U=liftVac H N p N U * i v U := by
    have he := hm.exact_match v U
    have hj : (H.S.a N:ℂ)^d ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos N).ne')
    rw [show Z v U=_ from he, initial]
    simp only [liftVac,i,t,Pi.smul_apply,smul_eq_mul]; field_simp
  have hp : Ledger F _ V.plays := ⟨⟨fun _ _ => rfl,fun _ _ => rfl⟩,⟨fun _ _ => (add_zero _).symm,fun _ _ => (smul_zero _).symm⟩,hm.linear,fun _ => rfl⟩
  refine ⟨⟨hp,fun v => ⟨hm.uses v,hm.bound v⟩,fun _ => rfl,fun v => ?_,?_,fun _ _ => rfl,rfl,?_,?_⟩,
    fun _ => rfl,fun _ => rfl,fun _ => le_rfl, hm.exact_match⟩
  · exact le_mul_of_one_le_left (Work.G08.size_nonneg ..) (H.levels.params _).columns_ge
  · intro x j; change F.coeffSize (F.core (x+j)) ≤ _; rw [map_add]; exact Size.add F ..
  · change IsLinearMap ℂ Z
    have he : IsLinearMap ℂ i := by
      constructor
      · intro a b; funext U; simp [i,SectionData.places,S.eval_linear.map_add]
      intro a b; funext U; simp [i,SectionData.places,S.eval_linear.map_smul]
    constructor
    · intro a b; funext U; simp [ha,he.map_add,mul_add]
    intro a b; funext U; simp [ha,he.map_smul]; ring
  · have hbar (x : F.Coeff) : i (star x)=star (i x) := by
      unfold i
      have ht : F.scaled t⁻¹ (star x)=star (F.scaled t⁻¹ x) := funext fun j => by simp
      funext U; rw [ht]; exact hS.ordinary_real ..
    have ht (s : Signed) (v) (U) : i (F.act s.ortho v) U=i v (pull s 0 U) := by
      unfold i; rw [S.placed_signed hS, F.scaling]; simp [affine]
    intro v s; funext U
    change scalar s (Z v (pull _ _ U))=Z (Motion.patch F s v) U
    simp only [ha,scalar_mul,vac_pull H N p N h le_rfl]
    rw [show scalar s (liftVac H N p N U)=liftVac H N p N U from scalar_real ..]
    unfold scalar Motion.patch; split
    · rw [hbar]; simp [ht]
    rw [ht]

variable (B : Authorities G) (W : Worth) (ref : ℕ → ℕ)

/-- Output of a `SOURCE_HISTORIES` call on the directed recipe's rep,
including its actual source entrance, not just equality of representation as
a bare unmasked function. -/
structure Scored (T : ∀ d N p, TransferData (B.frames.level d) H N p) : Prop where
  room : roomCost H.levels W
  bank : Bank W H.levels
  reads : RefLi H B.frames B.entry B.hol ref
  issued : (Family.mk H B.hol B.frames B.entry ref T).Makes
  trace d N p : ref d ≤ N → ∃ M : Music (B.frames.level d) H N p,
    M.tone N=voice (B.entry d) H N p ∧ Sung (B.entry d) H N p B.hol W (ref d) M ∧
      (T d N p).entries = (M.draft H).inits

variable {H B W ref}

theorem score (hp : H.Selected) (hr : roomCost H.levels W) (hb : Bank W H.levels)
    (he : ∀ d N p, ref d ≤ N → Mark.Prepared H (B.entry d) B.hol N p 0) (hC : RefLi H B.frames B.entry B.hol ref)
    (asks : ∀ d N p m,ref d ≤ m → m<N → ∃ C η T, Buys H (B.frames.level d) W m C η ∧ AtomStep (B.entry d) H N p m B.hol T C η) :
    ∃ T, Scored H B W ref T := by
  classical
  have issue (d N p) : ∃ T : TransferData (B.frames.level d) H N p, ref d ≤ N → T.Based B.hol (B.entry d) (ref d) ∧
      ∃ M : Music (B.frames.level d) H N p, M.tone N=voice (B.entry d) H N p ∧
        Sung (B.entry d) H N p B.hol W (ref d) M ∧ T.entries=(M.draft H).inits := by
    by_cases ht : ref d ≤ N
    · obtain ⟨M,hM,hS⟩ := pursue (B.entry d) H N p B.hol W hp hr hb (ref d) ht _ (uses (B.entry d) _ N p hp (B.sound d) (he d N p ht)) (asks d N p)
      obtain ⟨T,hU,hT⟩ := Work.G08.answer W H hr hb N p d (ref d) _ (M.draft H) (B.entry d) _
        (Sung.clocks _ H N p _ W _ M hS)
      exact ⟨T,fun _ => ⟨hT,M,hM,hS,hU⟩⟩
    exact ⟨⟨fun _ v => primary 0 v,LinearEquiv.refl ℂ _⟩, fun u => False.elim (ht u)⟩
  choose T hT using issue
  exact ⟨T,hr,hb,hC,⟨hp,hC.gets,hC.order,hC.fits,fun d N p hr o v => hC.loaded d N hr _ rfl rfl _ o v,
    fun d N p ht => (hT d N p ht).1⟩, fun d N p ht => (hT d N p ht).2⟩
end YM.Further.IterationRecipe
