import YM.Next.WARD_BIN.Clients
import YM.Next.WARD_BIN.Hats

/-!
# Cursor to comparison pages

Rank at cutoff, not rank of continuum monitor. One set of Page obligations for
all uses, *prices* visible: RPre must meet these and subsequently any
multimarker barriers too. `Chart` independent of schedule in the sense that
Atlas + Loans can be supplied given just the section/frame/H (see
`Gallery.credits`). Hung from C here to allow reading consistently only!

Not claiming W.Op duets come with arbitrary Producer histories, retain pages
and appropriate slots BEFORE choice. `Bearing`: at one (d,N,p) adms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter Wilson Lattice RG Labels Source Source.Drops Bid Work.G07 Work.G08
open scoped BigOperators Topology Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {d N p : ℕ} {W : Worth}
abbrev Gala (C : Family G) (d : ℕ) := Gallery d C.params C.labels C.localSection
structure Chart (C : Family G) (d : ℕ) where
  art : Gala C d
  tags : art.Loans

lemma pricing {Z : Frames G} {H : Hol G} (X : ∀ i,SectionData (Z.level i)) (h : ∀ i, (X i).Sound H)
    (hp : ∀ i,Bid.pop (X i)) (d : ℕ) : ∃ G : Gallery d H Z X, Nonempty G.Loans := by
  obtain ⟨v⟩ := populate d H Z X
  exact ⟨v,v.credits h hp⟩

namespace Chart
variable (A : Chart C d)

def ush (n : ℕ) := A.tags.sect (C.path.levels.params n).order (C.path.levels.params n).power
def uscore (n : ℕ) := A.tags.score (C.path.levels.params n).order (C.path.levels.params n).power
def snow (n : ℕ) := 1+2*(Real.exp (C.path.levels.params n).supportExponent*(1+ush A n))
lemma shu (n) : 1 ≤ ush A n := (A.tags.canon ..).1

lemma one_score (n) : 1 ≤ uscore A n := (A.tags.bill ..).1

/-- Single stage reserve. A pure threshold on stage constants, `loans`
obtained after sections before any L. Needed also on handoff to Mark/W.Close.
No hypothesis on how many copies after this -- different work.
-/
def Green := ∀ᶠ N in atTop, A.snow N*A.uscore N ≤ A.tags.mark*(rentAt C N)



/-- Finite equation contents at *actual* β and threshold. -/
def crate (N p) := A.art.basis.tree A.art.rays (C.beta N p) (face C N p).threshold
def tags_top (N p) := A.art.basis.xTree A.art.rays A.art.sees (C.beta N p) (face C N p).threshold

def jukes (D : Page C d N p) : PureBasis.Grid G d→ₗ[ℂ] C.label d :=
  IsLinearMap.mk' (fun u => D.refLabel A.art.cover (A.crate N p u) (A.tags_top N p u))
    (D.reference_linear _ _)

structure Bearing (N p : ℕ) : Prop where
  room : FitsIn A.art.cover (C.side N p)
  owns : stipend C.params (C.localSection d) (face C N p) A.art.cover (spot C N p) (A.ush N)
  easy : inkage (face C N p) (native C N p A.art.cover) d (cash C N) (κ C.path N)
  tips (c : ℝ) : 0≤c → Page.tip c (A.ush N) C A.art.cover N p ≤ snow A N*c
  pride (i) : Coin C.params (brim C d) A.art.cover (face C N p).order (face C N p) (spot C N p)
              (A.crate N p i) (A.tags_top N p i) (A.uscore N*‖i‖)
  light : snow A N*uscore A N ≤ A.tags.mark*rentAt C N
  truth (x) : A.tags.mark*‖x‖ ≤ ‖coat (brim C d) (face C N p).threshold (tags_top A N p x)‖

lemma oft (hG : G.Simple) (hC : C.Makes) (h : A.Green) : ∀ᶠ n in atTop,∀ p,Bearing A n p := by
  have hp := headway hC hG A.tags.live.2
  filter_upwards [hp,tooth hC A.art.cover hG, fits_event A.art.cover C.S,h,ink_event A.art.cover d hC hG] with n hi ht hv hg hb p
  let b:=face C n p
  have hx : b=C.path.levels.budget n := (hC.wilson.represents n p n le_rfl).vac
  let k := (C.path.levels.params n).order
  let P := (C.path.levels.params n).power
  have hr : b.order=k := hx ▸ rfl
  have hs : b.power=P := hx ▸ rfl
  have he := hv p
  refine ⟨he, (A.tags.canon k P).2 _ he b hr hs (spot C n p), hb p,fun c hc => ?_,fun v => ?_, hg,fun x => ?_⟩
  · have hm : b.supportExponent=(C.path.levels.params n).supportExponent := hx ▸ rfl
    refine mul_le_mul_of_nonneg_right (show sif b (native C n p _) (A.ush n)≤snow A n from ?_) hc
    have hu := ht p (spot C n p)
    have hz : (coverNumber b.B (native C n p A.art.cover):ℝ) ≤ 1 := by exact_mod_cast hu
    unfold sif snow BudgetPoint.mass; rw [← hm]; refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_of_le_one_right b.exponent_pos.le hz)) (by linarith [shu A n])) (by norm_num))
  · change Coin _ _ _ b.order _ _ _ _ _
    rw [hr]; exact (A.tags.bill k P).2.1 _ he b hr hs _ _ _ (rated hC p n).1 (covers_coupling hC p n)
  change _ ≤ ‖(brim C d).scaled b.threshold ((brim C d).coords _)‖; unfold tags_top; rw [A.art.basis.top_tree _ _ _ _ _ b.threshold_pos]; exact hi p x

lemma cost_of_mark {D : Page C d N p} (h : D.Works A.art.cover W) (hc : C.Makes)
    (hp : A.Bearing N p) (hC : roomCost C.path.levels W) (hv : Bank W C.path.levels) (v : PureBasis.Grid G d) :
    A.tags.mark/2 * ‖v‖ ≤ (brim C d).coeffSize ((C.factory d N p).terminal.symm (A.jukes D v)) := by
  let t := coat (brim C d) (face C N p).threshold (A.tags_top N p v)
  obtain ⟨R,hR,_,hr,-⟩ := D.flush hc hC hv h hp.room (hp.pride v) hp.easy (A.shu N) hp.owns
    (hp.tips _ (mul_nonneg (zero_le_one.trans (one_score A N)) (norm_nonneg _)))
  have HH := hR.wind hC hv
  let B := (C.factory d N p).terminal.symm (A.jukes D v)
  have he : (R.voice N).x=B-t := hr
  have hx : 1 ≤ rentAt C N := (C.path.levels.params N).columns_ge
  have hz : 0 < rentAt C N := zero_lt_one.trans_le hx
  have hw : 16*(brim C d).coeffSize (B-t) ≤ A.tags.mark * ‖v‖ := by
    rw [he] at HH
    apply le_of_mul_le_mul_right _ hz
    have hu := (mul_le_mul_of_nonneg_right hp.light (norm_nonneg v))
    linarith only [HH, size_nonneg (brim C d) (B-t), hu]
  have hB : (brim C d).coeffSize t ≤ (brim C d).coeffSize B + (brim C d).coeffSize (B-t) := by rw [size_sub_rev _ B t]; exact size_triangle _ _ _
  have ht : A.tags.mark*‖v‖ ≤ (brim C d).coeffSize t := (hp.truth v).trans (coeff_le t)
  nlinarith only [hp.truth v,hB,hw,ht,norm_nonneg v,A.tags.live.1]

lemma record (D : Page C d N p) (hw : D.Works A.art.cover W) (hc : C.Makes)
    (hp : A.Bearing N p) (hC : roomCost C.path.levels W) (hv : Bank W C.path.levels) : Injective (A.jukes D) := by
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun i hi => ?_))
  have hh := A.cost_of_mark hw hc hp hC hv i
  rw [hi,map_zero,show (brim C d).coeffSize 0=0 by simp [Frame.coeffSize]] at hh
  exact norm_le_zero_iff.mp (le_of_mul_le_mul_left (by simpa using hh) (half_pos A.tags.live.1))
end Chart

/-- Input of common shelf of Pages: even if engine constructors begin at
later cutoff than ref, bookkeeping aligns that tail. No assuming target data
reachable from the chosen path. -/
structure Shelf (A : Chart C d) where
  horizon : ℕ
  page N p : horizon ≤ N → Page C d N p

namespace Shelf
variable {A : Chart C d} (Z : Shelf A)

structure Assured (W : Worth) : Prop where
  reserves : A.Green
  aligns : ∀ N p, ∀ h : Z.horizon ≤ N,(Z.page N p h).Works A.art.cover W

def panel (x : ℕ×ℕ) : PureBasis.Grid G d→ₗ[ℂ] C.label d := if h : Z.horizon ≤ x.1 then A.jukes (Z.page x.1 x.2 h) else 0
lemma panel_event (h : Z.Assured W) (hp : C.Makes) (hG : G.Simple) (hC : roomCost C.path.levels W) (hv : Bank W C.path.levels) :
    ∀ᶠ N in atTop, ∀ p, Injective (Z.panel (N,p)) := by
  filter_upwards [eventually_ge_atTop Z.horizon, A.oft hG hp h.reserves] with N hN hi p
  unfold panel; rw [dif_pos hN]; exact A.record _ (h.aligns N p hN) hp (hi p) hC hv
end Shelf
end YM.WardBin
