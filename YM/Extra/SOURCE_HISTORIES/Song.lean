import YM.Extra.SOURCE_HISTORIES.Birth
import YM.Extra.SOURCE_HISTORIES.Replay

/-!
# Placed composition . Output choices pinned.

Call birth and the one-level theorem on every step where the stencil and
costs fit. This is an **actual construction conditional** on precise
one-block analytic estimates, sufficient entrance prices and address shelf,
on a supplied history. Includes N=reference. No need to adjust stages after
the construction; have to pass these same prices in!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G)

structure Music (F : Labels.Frame G d) (H : History G) (N p : ℕ) where
  tone : ∀ m, Voice F H p m

namespace Music
variable {N p} (V : Music F H N p)

def draft : Paper H N p F where
  inits m := (V.tone m).plays
  paid m := (V.tone m).charge
end Music

/-- The top always uses the fixed B and frame F, same shelf & chosen
docket for all v. -/
def topVoice (Y : Shelf (H.rep N p N).activities) (q : ℕ) : Voice F H p N where
  plays := born B _ 0 Y q
  charge v := F.coeffSize (F.core v)
  index := LinearEquiv.refl ℂ _

structure OnTop (V : Voice F H p N) : Prop where
  heard : Heard B H N p A N V
  out v : (V.plays v).x = v
  germ v : (V.plays v).regular=0
  cost v : V.charge v ≤ F.coeffSize (F.core v)
  earns v U : (V.plays v).density 0 B (H.rep N p N) U = ((H.S.a N:ℂ)^d)*
     ((H.rep N p N).eval U:ℂ) * initial B H N p v 0 U

theorem onTop (h : H.Selected) (hS : B.Sound A) (Y : Shelf (H.rep N p N).activities) (q : ℕ) {C : ℝ} (hc : 1 ≤ C)
    (ht : ∀ (i : F.Index) (U : Config G (H.S.side N p)), ‖B.places (Size.axis F i) 0 U‖ ≤ C)
    (he : fee F (H.levels.budget N) (B.footprint (0:Site (H.S.side N p))) C (H.levels.clock.forcedAllowance N) ≤
      Real.sqrt (H.levels.clock.forcedAllowance N)) : OnTop B H N p A (topVoice B H N p Y q) := by
  let R := H.rep N p N
  have hv : R.p = H.levels.budget N := (h.represents N p N le_rfl).vac
  obtain ⟨hp,hs⟩ := launched B R 0 Y hS (h.represents N p N le_rfl).good (forcedPos _ N) hc ht (hv.symm ▸ he) q
  let V := topVoice B H N p Y q
  let t := H.levels.clock.threshold N
  have hb : R.p.threshold=t := congr_arg BudgetPoint.threshold hv
  let i (v : F.Coeff) := B.places (F.scaled t⁻¹ v) (0:Site (H.S.side N p))
  let Z (v) := (V.plays v).density 0 B R
  have ha (v U) : Z v U=liftVac H N p N U * i v U := by
    unfold i; rw [← hb]; exact (hs v).2.2 U
  refine ⟨⟨hp,fun v => ⟨(hs v).1,(hs v).2.1⟩,fun _ => rfl,fun v => ?_,?_,fun _ _ => rfl,rfl,?_,?_⟩,
    fun _ => rfl,fun _ => rfl,fun _ => le_rfl,fun v U => ?_⟩
  · exact le_mul_of_one_le_left (Work.G08.size_nonneg ..) (H.levels.params _).columns_ge
  · intro i j; change F.coeffSize (F.core (i+j)) ≤ _; rw [map_add]; exact Size.add F ..
  · change IsLinearMap ℂ Z
    have he : IsLinearMap ℂ i := by
      constructor
      · intro a b; funext U; simp [i,SectionData.places,B.eval_linear.map_add]
      intro a b; funext U; simp [i,SectionData.places,B.eval_linear.map_smul]
    constructor
    · intro a b; funext U; simp [ha,he.map_add,mul_add]
    intro a b; funext U; simp [ha,he.map_smul]; ring
  · have hbar (x : F.Coeff) : i (star x)=star (i x) := by
      unfold i
      have ht : F.scaled t⁻¹ (star x)=star (F.scaled t⁻¹ x) := funext fun j => by simp
      funext U; rw [ht]; exact hS.ordinary_real ..
    have ht (s : Signed) (v) (U) : i (F.act s.ortho v) U=i v (pull s 0 U) := by
      unfold i; rw [B.placed_signed hS, F.scaling]; simp [affine]
    intro v s; funext U
    change scalar s (Z v (pull _ _ U))=Z (Motion.patch F s v) U
    simp only [ha,scalar_mul,vac_pull H N p N h le_rfl]
    rw [show scalar s (liftVac H N p N U)=liftVac H N p N U from scalar_real ..]
    unfold scalar Motion.patch; split
    · rw [hbar]; simp [ht]
    rw [ht]
  change Z v U = _
  rw [ha,initial]
  have hj : (H.S.a N:ℂ)^d ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos N).ne')
  simp only [liftVac,i,t,Pi.smul_apply,smul_eq_mul]; field_simp

variable (W : Worth)

structure Sung (r : ℕ) (V : Music F H N p) : Prop where
  head : OnTop B H N p A (V.tone N)
  ahead : r ≤ N
  earned m (hm : r ≤ m) (ht : m ≤ N) : Heard B H N p A m (V.tone m)
  step m (hm : r ≤ m) (ht : m<N) : Responds B H N p W m (V.tone (m+1)) (V.tone m)

theorem Sung.clocks (r : ℕ) (V : Music F H N p) (h : Sung B H N p A W r V) : Paper.Clocks (V.draft H) B A W r := by
  refine ⟨h.ahead, fun m hm hp => (h.earned m hm hp).earns,h.head.cost,fun m hm hp => (h.step m hm hp).tally,
    fun m hm hp => (h.step m hm hp).values,h.head.earns,fun v => ⟨h.head.out v,h.head.germ v⟩,fun i hi he => ?_,
    fun i hi he => ?_,fun i hi he v => ?_⟩
  · have ht := h.earned i hi he; exact (ht.currents _).trans ht.unit
  · have he := (h.earned i hi he).book; exact ⟨he.x,he.reg,he.f,he.tags⟩
  let y := V.tone i
  have he := h.earned i hi he
  have hf (s) : Motion.patch F s (y.plays v).x=(y.plays (Motion.patch F s v)).x := by
    unfold y; rw [he.currents,he.currents,he.moves]
  refine ⟨?_,fun s => (hf (s,false)).symm⟩
  have ha := (hf (1,true)).symm
  unfold Motion.patch at ha; simp only [if_true] at ha
  simpa only [Music.draft,y,show (1:Signed).ortho=1 from map_one Signed.inclusionO, Frame.act_one] using ha

/-- Compose to the chosen reference. Builds a `Music` with SAME topVoice,
and stronger `Heard` invariant at every fitted stage. -/
theorem pursue (h : H.Selected) (hw : roomCost H.levels W) (hb : Bank W H.levels) (r : ℕ) (hr : r≤N)
    (V : Voice F H p N) (hu : OnTop B H N p A V)
    (calls : ∀ m : ℕ, r ≤ m → m<N → ∃ (C η : ℝ), ∃ T : Heading F, Buys H F W m C η ∧ AtomStep B H N p m A T C η) :
    ∃ M : Music F H N p,M.tone N=V ∧ Sung B H N p A W r M := by
  classical
  induction hr using Nat.decreasingInduction with
  | self =>
    let a (m : ℕ) : Voice F H p m := ⟨fun _ => primary 0 0, fun _ => 0,LinearEquiv.refl ℂ _⟩
    let M : Music F H N p := ⟨update a N V⟩
    have he : M.tone N=V := update_self N V a
    refine ⟨M,he,⟨he.symm ▸ hu, le_rfl, fun i hi ht => ?_, fun i hi ht => by omega⟩⟩
    obtain rfl : i=N := le_antisymm ht hi
    rw [he]; exact hu.heard
  | of_succ k hk ih =>
    obtain ⟨M,hM,hS⟩ := ih fun i hi => calls i (by omega)
    obtain ⟨C,η,T,hT,hQ⟩ := calls k le_rfl hk
    obtain ⟨v,hv,hV⟩ := reprise B H N p A W k (M.tone (k+1)) h hk (hS.earned (k+1) le_rfl hk) hw hb T hQ hT
    let t : Music F H N p := ⟨update M.tone k v⟩
    have hh : t.tone k=v := update_self k v M.tone
    have hu (i : ℕ) (hi : k < i) : t.tone i=M.tone i := update_of_ne hi.ne' v M.tone
    refine ⟨t,(hu N hk).trans hM,?_,hk.le, fun i hi he => ?_,fun i hi he => ?_⟩
    · rw [hu _ hk]; exact hS.head
    · obtain h|h := lt_or_eq_of_le hi
      · rw [hu _ h]; exact hS.earned i h he
      subst i; rw [hh]; exact hv
    obtain h|h := lt_or_eq_of_le hi
    · rw [hu i h,hu (i+1) (by omega)]; exact hS.step i h he
    subst i; rw [hu (k+1) k.lt_succ_self,hh]; exact hV

end YM.Extra.Histories
