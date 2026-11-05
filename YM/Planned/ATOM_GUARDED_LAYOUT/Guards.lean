import YM.Extra.SOURCE_HISTORIES.Song
import YM.Planned.ATOM_GUARDED_LAYOUT.Assembly
import YM.Progress.DIRECTED_RECIPE.Pellets
import YM.Push.LOCAL_SPLITTING.Padding


/-!
# Weaken JUST the one-block/top slot hypotheses without ANY padding

`Register` and `PerBlock` can already be used where the *given* Slots and
Shelf types in those ports are available. But:

For example on the population layout of DirectedRecipe proving even
ONE relevant `Slots`, much less `Shelf`, is literally impossible
(check below). This can bite e.g. if hoping to apply the Local atom
work/integral estimates to that recipe after construction. At least for
these source calls there is a cheaper solution than doing *any* padding
at all. Use the weaker shape-allocation condition. We show how to adapt
the conversion proofs without asking again for any of the occurrence
or read estimates, by introducing a scratch dictionary in that
combinatorial proof ONLY -- performing the source insert in place on
the given activities and refs with every original mask, label number,
vacuum/path, normalizer and support remaining as is. In particular no
invoking Analytic proposals on a changed Selected history. All addresses
ultimately used meet the original, not weakened, predicates. Not addressing
the more general TOPOLOGY_SAFE_PADDING task or simultaneous trajectories.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.GuardedAtom.Guard
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Push.Local Next.Foundations Extra.Histories
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {n : Side} {A : Activities G n}

open Progress.DirectedRecipe

variable {Z : BudgetPoint} (h : HasSlots Z A)

include h










omit h

variable {ι : Type*}
structure Berths (Z : BudgetPoint) (A : Activities G n) (X : ι → Support n) where
  label : Letters A X ↪ ℕ
  support (s) : (A.forced (label s)).support = s.total
  inventory (s) : (A.forced (label s)).inventory = s.keeps
  pass (s) U : (A.forced (label s)).support ∩ flags Z.threshold U = (A.forced (label s)).inventory →
    (A.forced (label s)).extraTest U

/-- Same *number* of addresses as if using Shelf or the sleep register,
no hypothesis of blank K needed for Local calls themselves. -/
structure Keeper (Z : BudgetPoint) (A : Activities G n) where
  code : Dummy n ↪ ℕ
  support (s) : (A.forced (code s)).support = s.1.val.1
  inventory (s) : (A.forced (code s)).inventory = s.1.val.2
  pass (s) U : (A.forced (code s)).support ∩ flags Z.threshold U = (A.forced (code s)).inventory →
    (A.forced (code s)).extraTest U

namespace Keeper
/-- HasSlots imports directly. -/
private def key : Dummy n ↪ Foot n × ℕ where
  toFun s := (⟨s.1.val.1,s.1.val.2,s.1.property.1,s.1.property.2⟩,s.2)
  inj' _ _ hx := Prod.ext (Subtype.ext (Prod.ext (congr_arg (fun x => x.1.support) hx) (congr_arg (fun x => x.1.inventory) hx))) (congr_arg (fun t : Foot n × ℕ => t.2) hx)

def sufficient : Keeper Z A where
  code := key.trans (sleepK G n)
  support s := h.forced.symm ▸ congr_arg Foot.support (tile_exact (G:=G) Z (key s).1 s.2)
  inventory s := h.forced.symm ▸ congr_arg Foot.inventory (tile_exact (G:=G) Z (key s).1 s.2)
  pass s U := by
    rw [h.forced]
    intro hs
    change (Ovens.Pipes.addr (folio ..) Z (sleepK G n (key s))).extraTest U
    apply (tile_test Z (key s).1 s.2 U).2
    have he := tile_exact (G:=G) Z (key s).1 s.2
    exact (congr_arg₂ (fun x y : Foot n => x.support ∩ flags Z.threshold U = y.inventory) he he) ▸ hs

-- names for compatibility with birth further on
lemma blank (h : HasSlots Z A) (s : Dummy n) : A.K ((sufficient h).code s)=0 := h.forced_zero _

def supply (K : Keeper Z A) [Countable ι] (X : ι → Support n) : Berths Z A X := by
  letI := Classical.choice (nonempty_encodable (Letters A X))
  let f : Letters A X ↪ Dummy n := {
    toFun s := (⟨(s.total,s.keeps),s.keeps_ne,s.keeps_sub⟩, Encodable.encode s)
    inj' _ _ h := Encodable.encode_injective (congr_arg Prod.snd h) }
  exact ⟨f.trans K.code,fun _ => K.support _,fun _ => K.inventory _,fun _ => K.pass _⟩
end Keeper

/-- A scratch calculation ONLY. Do not take `Selected`, `Paper` etc. of
this thing in place of the given Family. `glazed` remembers original K (so
K histories unchanged) even on labels having other predicates, and preserves
the exact vacuum energy, gas/coats, activity numbers and principal paths,
masks, footprints. Only erase the flag extraTest's *receipt requirement*
temporarily at the construction of the new bookings. Every dependence of
K itself on those tests remains in force. And at the end restore EVERY
predicate, before consuming any `AtomStep`.
-/
private def glazed (A : Activities G n) : Activities G n := { A with
  forced := fun i => {A.forced i with extraTest:=fun _ => True} }

private def plate (R : Rep G n) : Rep G n := {R with activities:=glazed R.activities}

variable {d : ℕ} {F : Labels.Frame G d} {R : Rep G n} {Y : Hol G} {B : SectionData F} {o : Site n}
  {M : Raw F n} {η κ w a b c σ C Λ δ : ℝ}

private theorem lawful (hx : R.Lawful σ C Λ δ η) : (plate R).Lawful σ C Λ δ η := by
  let K := (glazed R.activities)
  have hu := hx.labels
  have hf := hu.forced
  have he : K.ForcedFamily R.p := ⟨hf.sym, fun _ _ _ => Iff.rfl, hf.meas, fun _ => MeasurableSet.univ, hf.reads, fun _ _ _ _ _ => rfl,
    fun i U h => ⟨(hf.permit i U h).1,trivial⟩⟩
  refine ⟨hx.paths,⟨hu.regular.smooth,hu.regular.at_flat,hu.regular.vanish⟩,he,fun s o => ?_,hu.boundE,hu.boundK⟩
  obtain ⟨m⟩ := hu.moves s o
  exact ⟨m.ep,m.kp,m.reg_site,m.reg_support,m.forced_support,m.forced_inventory,fun _ _ => Iff.rfl,m.valuesE,m.valuesK⟩

variable {X : ℕ → Support n}

private def layout (A : Activities G n) {ι : Type*} (X : ι → Support n) : Letters (glazed A) X ≃ Letters A X :=
  Equiv.sigmaCongrRight fun _i => (Equiv.refl (Finset ℕ)).subtypeEquiv
    (fun _x => ⟨fun h => ⟨h.1,h.2,h.3⟩,fun h => ⟨h.1,h.2,h.3⟩⟩)

private def schedule (S : Berths R.p R.activities X) : Push.Local.Slots (plate R).activities X where
  label := (layout R.activities X).toEmbedding.trans S.label
  support u := S.support ((layout R.activities X) u)
  inventory u := S.inventory ((layout R.activities X) u)
  allows _ _ := trivial

private theorem rawUp (hf : M.Format o X R) : M.Format o X (plate R) :=
  ⟨hf.origin,hf.regular,fun i U h => ⟨(hf.force.forcing i U h).1,trivial⟩,hf.force.carried,hf.force.invariant,hf.force.supported,hf.force.borel⟩

private theorem tally (hx : Tare M o X Y B R w η κ a b c) : Tare M o X Y B (plate R) w η κ a b c := by
  obtain ⟨e,h,h1,h2⟩ := hx.bulk
  exact ⟨⟨e,h,h1,h2⟩,hx.packets⟩

variable (S : Berths R.p R.activities (fun i => joint B o (X i)))

def mint (M : Raw F n) (Y : Hol G) : Coefficient F n := M.build o X Y B (plate R) (schedule S)



theorem usage (hf : M.Format o X R) (hh : R.Lawful σ C Λ δ η) (he : Readable Y B R.p n w) :
    (mint S M Y).Format o Y R := by
  have hx := Raw.build_format (schedule S) (lawful hh).labels.forced he (rawUp hf)
  refine ⟨hx.smooth,hx.origin,hx.identity_null,hx.projects,?_,hx.carried,hx.invariant,hx.supported,hx.borel⟩
  intro i U hu
  by_cases ht : M.forced i U ≠ 0
  · exact hf.force.forcing i U ht
  let f := fun i => rebate Y B o (X i) R.p.threshold (M.bulk i)
  have hP : (mint S M Y).forced i U ≠ 0 := hu
  have hc : (schedule S).pack R.p.threshold f i U ≠ 0 := by
    change M.forced i U + (schedule S).pack R.p.threshold f i U ≠ 0 at hu
    simpa only [not_not.mp ht,zero_add] using hu
  obtain ⟨s,hs⟩ : ∃ s,S.label s=i := by
    by_contra hn
    exact hc (by rw [Push.Local.Slots.pack_none _ _ _ _ ?_]; rfl; rintro ⟨q,hq⟩; exact hn ⟨layout _ _ q,hq⟩)
  subst i
  have he : (glazed R.activities).forced (S.label s) |>.eligible R.p.threshold U := hx.forcing _ _ hP
  exact ⟨he.1,S.pass _ _ he.1⟩

lemma tab_mint (hf : M.Format o X R) (hh : R.Lawful σ C Λ δ η) (hκ : 0<κ)
    (he : Readable Y B R.p n w) (hx : Tare M o X Y B R w η κ a b c) : Tab (mint S M Y) o R κ a (b+c) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := (tally hx).tab (schedule S) hκ (lawful hh).labels.boundK he (rawUp hf)
  exact ⟨h1,h2,h3,h4,h5⟩

lemma value_mint (hf : M.Format o X R) (hh : R.Lawful σ C Λ δ η) (hκ : 0<κ)
    (he : Readable Y B R.p n w) (hx : Tare M o X Y B R w η κ a b c) : (mint S M Y).density o B R = M.eval o X B R := by
  have he₁ := Raw.build_density (schedule S) (lawful hh) he (rawUp hf) ((tally hx).income hκ le_rfl) hκ
  have ha : ∀ P : Coefficient F n, P.density o B (plate R)=P.density o B R := by
    intro P; funext i; unfold Coefficient.density; congr 2 -- each eval, marked, p threshold
  have hM : M.eval o X B (plate R)=M.eval o X B R := by funext i; unfold Raw.eval; congr 2
  exact ((ha _).symm.trans he₁).trans hM

lemma size_mint (hf : M.Format o X R)
    (he : Readable Y B R.p n w) (hx : Tare M o X Y B R w η κ a b c) (u : F.Coeff) :
    F.coeffSize ((mint S M Y).x-u) ≤ F.coeffSize (M.seed - u) + a :=
  (tally hx).canonical_cost (schedule S) he (rawUp hf) u


lemma sensor (hf : M.Format o X R) (he : Readable Y B R.p n w) (hx : Tare M o X Y B R w η κ a b c)
    {u : F.Coeff} {r} {g} (hu : Models Y o X R.p M u r g) (hr : 0≤r) :
    F.coeffSize ((mint S M Y).x-u) ≤ errorPrice Y F*r := compareModels (schedule S) he (rawUp hf)
      (Size.series F ((tally hx).row_cost he (rawUp hf)).2.1).of_norm hr hu

open Motion

variable (B) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ

/-- Weaker one-step layout port. Other bills unchanged except here write
the model vs seed accounting as an actual sum of alternative payment
options. -/
def Promise (f : g₀) (lead : F.Coeff) (w t r : ℝ) :=
    ∃ (X : ℕ → Support WorkSite) (M : Raw F WorkSite) (a b c : ℝ), Arrival B H N p i f X M ∧
      Nonempty (Berths (Rout).p (Rout).activities (fun q => joint B 0 (X q))) ∧
      Tare M 0 X Y B Rout w (H.levels.clock.forcedAllowance i) (kappa H i) a b c ∧
      turnCost (Rout).p.order (Rout).p.power*a+(b+c) ≤ r ∧
        ((∃ (g : ℕ → Directions G WorkSite → ℂ) (e : ℝ), Models Y 0 X (Rout).p M lead e g ∧ 0≤e ∧ orbitCost F*(errorPrice Y F*e) ≤ t) ∨
          orbitCost F*(F.coeffSize (M.seed-lead)+a) ≤ t)

structure Coin (L : F.Coeff →ₗ[ℂ] F.Coeff) (C η w : ℝ) : Prop where
  main m : m≠0 →
    let x := Size.axis F m
    Promise B H N p i Y ((Extra.Histories.primary 0 x).density 0 B (Old))
      (L (vowel F (H.S.block i) x)) w (η*F.coeffSize (F.core x)) (C*F.coeffSize (vowel F (H.S.block i) (F.core x)))
  regular (f : g₀) (b : Support StartSite) (c : ℝ) : let u := η*(Old).p.mass b c
    RegFit (Old) 0 d Y b f → (Old).p.supBounds 0 b f c → Promise B H N p i Y (salary (Old) b f) 0 w u u
  forced (f : g₀) (m : ℕ) (c : ℝ) : let u := η*((Old).p.mass ((Old).activities.forced m).support c/kappa H (i+1))
    SlotFit (Old) 0 m f → 0≤c → (∀ U, ‖f U‖ ≤ c) → Promise B H N p i Y (fare (Old) m f) 0 w u u

variable {B H N p i Y} {L : F.Coeff →ₗ[ℂ] F.Coeff} {t r : ℝ}

lemma Promise.paid {g : g₀} {v} (h : Promise B H N p i Y g v w t r) (he : H.Conv N p i) (hT : Readable Y B (Rout).p WorkSite w) :
    PaidAtom B H N p i Y g v t r := by
  obtain ⟨X,M,a,b,c,⟨hf,hh⟩,⟨S⟩,hx,hR,hP⟩ := h
  have hD := usage S hf he.good hT
  have hκ := Real.sqrt_pos.mpr (forcedPos H.levels i)
  have hJ := tab_mint S hf he.good hκ hT hx
  refine paid_center (fun s => he.good.labels.moves s 0) hT.sound hD ((value_mint S hf he.good hκ hT hx).trans hh) hJ ?_ hR
  obtain ⟨f,e,h1,h2,h3⟩ | hP := hP
  · exact le_trans (mul_le_mul_of_nonneg_left (sensor S hf hT hx h1 h2) (zero_le_one.trans (orbitCost_one_le F))) h3
  exact le_trans (mul_le_mul_of_nonneg_left (size_mint S hf hT hx v) (zero_le_one.trans (orbitCost_one_le F))) hP




variable (H C r)








section summit
-- The SAME History all the way -- compute just the (algebraic) `OnTop`
-- candidate on an extraTest-erased copy *of the top layout*; since the
-- sealed addresses we actually use there are guaranteed anyway whenever
-- geometric eligibility holds, get OnTop on the original. No moves, steps,
-- analytic costs or advances *supplied* on a modified layout. This doesn't
-- solve the recipe issue of Aperture, at all. And even here Shelf for

-- proved IMPOSSIBLE there), so this path produces a `Makes` and calibration
-- alternative common witness but not `Issue.Printed` for it. Also doesn't
-- reprice or reprovision any recipe.
private def display (H : History G) : History G := { H with
   rep := fun N p m => plate (H.rep N p m) }

private lemma choice (h : H.Selected) : (display H).Selected := by
  refine ⟨h.path_shared,fun N p m hm => ?_, fun N p => ?_,fun N p m hm => ?_,h.reaches,h.running⟩
  · obtain ⟨a,b,c,d⟩ := h.represents N p m hm; exact ⟨a,b,lawful c,d⟩
  · obtain ⟨ha,he⟩ := h.starts N p; refine ⟨ha,?_⟩
    funext x; exact congr_fun he x
  obtain ⟨ha,hc⟩ := h.steps N p m hm; refine ⟨?_,hc⟩
  funext x
  let R := H.rep N p m; let K := H.rep N p (m+1)
  have hh {s : Side} (R : Rep G s) : (plate R).eval=R.eval := rfl
  change (plate R).eval x = (H.levels.clock.op m p).push K.beta (plate K).eval x
  rw [hh,hh]; exact congr_fun ha x

private def demo {K : Keeper Z A} (hs : ∀ s,A.K (K.code s)=0) : Shelf (glazed A) := ⟨K.code,K.support,K.inventory,fun _ _ => trivial,hs⟩

variable (F B) (H : History G) (N p : ℕ) (ℓ : Keeper (H.rep N p N).p (H.rep N p N).activities) (he : ∀ s,(H.rep N p N).activities.K (ℓ.code s)=0)

/-- The top Voice at the given berth layout. Defines ACTUAL coefficients
on this History. They will be shown to meet every original Form and receive
the exact same cost; there is no choice-through-padding or AE update of flags.
-/
def summit (q : ℕ) : Voice F H p N :=
  let V := topVoice B (display H) N p (demo he) q
  ⟨V.plays,V.charge,V.index⟩

lemma summon (h : H.Selected) (q : ℕ) {C : ℝ} (hS : B.Sound Y) (hC : 1 ≤ C)
    (ht : ∀ (i : F.Index) (U : Config G (H.S.side N p)), ‖B.places (Size.axis F i) 0 U‖ ≤ C)
    (hf : fee F (H.levels.budget N) (B.footprint (0:Site (H.S.side N p))) C (H.levels.clock.forcedAllowance N) ≤
      Real.sqrt (H.levels.clock.forcedAllowance N)) : OnTop B H N p Y (summit F B H N p ℓ he q) := by
  have hs := onTop B (display H) N p Y (choice H h) hS (demo he) q hC ht hf
  let R := H.rep N p N
  let K := topVoice B (display H) N p (demo he) q
  -- Every nonzero forced term lands in the *very same* guaranteed address;
  -- geometry agrees and thus its extraTest too when used. Old predicates in
  -- unmarked paths, gas coverage etc haven't changed at all.
  have hy (v i U) (hh : ((summit F B H N p ℓ he q).plays v).forced i U ≠ 0) : (R.activities.forced i).eligible R.p.threshold U := by
    have h₀ := (((hs.heard).earns v).1.forcing i U hh).1
    change (R.activities.forced i).support ∩ flags R.p.threshold U = (R.activities.forced i).inventory at h₀
    refine ⟨h₀,?_⟩
    obtain ⟨s,rfl⟩ : ∃ s,ℓ.code s=i := by
      by_contra hx; apply hh
      let R' := plate R
      let X := B.footprint (0:Site (H.S.side N p))
      change Attach.line R' X (demo he) q _ i U=0
      rw [Attach.line_empty]
      · rfl
      rintro ⟨s,hs⟩
      exact hx ⟨_,hs⟩
    exact ℓ.pass _ U h₀
  have hv (v : F.Coeff) :
      (K.plays v).Format 0 Y R ∧ (K.plays v).remBound 0 R (Real.sqrt (H.levels.clock.forcedAllowance N)) (K.charge v) := by
    obtain ⟨hs,h1⟩ := hs.heard.earns v
    exact ⟨⟨hs.smooth,hs.origin,hs.identity_null,hs.projects,fun i U => hy v i U,hs.carried,hs.invariant,hs.supported,hs.borel⟩,h1⟩
  have hd : (fun v => (K.plays v).density 0 B (plate R)) = (fun v => (K.plays v).density 0 B R) := by funext v x; unfold Coefficient.density; congr 2
  have hi : (plate R).eval=R.eval := rfl
  refine ⟨⟨hs.heard.book,hv,hs.heard.currents,hs.heard.cone,hs.heard.summed,hs.heard.moves,hs.heard.unit,
    hd ▸ hs.heard.values,fun v y => ?_⟩,hs.out,hs.germ,hs.cost,fun v U => ?_⟩
  · have he := hs.heard.travels v y
    change dance y ((K.plays v).density 0 B (plate R)) = _ at he
    change dance y ((K.plays v).density 0 B R)=_
    exact (congr_arg (dance y) ((congr_fun hd v).symm)).trans (he.trans (congr_fun hd _))
  have hs := hs.earns v U
  change (K.plays v).density 0 B (plate R) U = ((H.S.a N:ℂ)^d)*((plate R).eval U:ℂ)* initial B H N p v 0 U at hs
  change (K.plays v).density 0 B R U= _
  rwa [show (K.plays v).density 0 B R = _ from (congr_fun hd v).symm,← show (plate R).eval U=R.eval U from congr_fun hi U]
end summit

open Org Supply
variable {M : Metals G} {V : Rolls M.p} {A : Alloy M V}



end YM.Planned.GuardedAtom.Guard
