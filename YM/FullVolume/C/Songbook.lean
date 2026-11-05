import YM.FullVolume.C.Ribbon
import YM.FullVolume.Rods

/-! Chord at all phases. Constructor can do advance with the same primitive results and not reselect ordinal at a new β. Path,Towers remain same.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Mallow Marlin Trio
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    (R: Factor A) {N m n:ℕ}
local notation "X'" => A.B.a.S
local notation "I" => Rep G (A.B.a.S.side (m+1) n)
local notation "Ω" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "e" => Trio.base (Rain.lint R.target A m) (radiusB Ω)
local notation "k" => Rain.lint R.target A m
local notation "γ"=> A.B.kin.alpha N m
variable {c c₁: ℝ} {R}
namespace Chord
variable (W:Chord R N m n c c₁) (Y:Flight A N m n)
local notation "g₀" => Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) Ω
-- threshold cap explicit. use any lift (no extraction). Literal function and family bounds.
def bright (R:Factor A)(m:ℕ)(c c₁:ℝ) :=
    (((c+2*c₁)*forecastE A.B.a m + turnFee (A.B.a.budget m)*Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) + Boulevard.gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) + turnFee (A.B.a.budget m)*(gleam (C:=R.target) (m:=m) (A:=A)*Real.exp (preExponent (A.B.a.budget m)* coverTicket (Rain.lint R.target A m))))
lemma fill_price : Collection.Local (W.listing Y) B (W.source Y) (bright R m c c₁) (forecastK A.B.a m R.scout Y.val.beta) := by
  let F:ℝ→Rep G (A.B.a.S.side (m+1) n):= fun _=> Y.val; have he: ∀ x ∈ Set.Icc 0 0,Lives (spatial A).bake N (m+1) n (F x)∧(F x).beta∈band A.B.a (m+1):=fun _ _ => Y.property
  have h₀:= Set.left_mem_Icc.mpr (show (0:ℝ)≤0 from le_rfl)
  have hv:Curve (A.B.a.budget (m+1)) F (Set.Icc 0 0):= by rw [← (show _=A.B.a.budget (m+1) from Y.property.1.point)]; exact unchanged ..
  obtain ⟨U,-⟩:= verdict W.earns W.paid hv he h₀
  obtain ⟨hk,hu⟩:= (W.credit (Rain.listIn (F 0))).emits F U hv he rfl 0 h₀
  obtain ⟨ha,hL,-⟩:= W.at_turn U h₀ hv he
  change W.listing Y=_ at ha
  change W.source Y=_ at hL; rw [ha,hL]; exact Rain.primed W.earns W.paid U hv he R.inn (R.settles _ _) W.tone (W.order _) 0 h₀ hk hu
lemma lightning (l : ℝ) : finish (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m)
    (shelves (W.listing Y) (A.B.kin.path N m) (A.B.a.budget m))
    (branch (W.listing Y) (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) (W.source Y) (A.B.kin.alpha N m))
    ((W.moment Y).beta) l={(W.moment Y) with v:=l} := by unfold moment Return.result Template.install Template.trial board; rw [A.B.bases]; rfl

def sails (r:Rep G (A.B.a.S.side m n))(t:I) := ∃ y:Chord.Flight A N m n, y.val=t ∧ r=W.moment y

lemma sails_singleton {u v t} (h: W.sails u t) (h':W.sails v t): u=v:= by
  obtain ⟨y,rfl,rfl⟩:=h; obtain ⟨x,ht,rfl⟩:=h'
  exact congr_arg _ (Subtype.ext ht.symm)
lemma spores (r v:ℝ) (h:r≤v) (Q : ℝ → I) (hp:Curve (A.B.a.budget (m+1)) Q (Set.Icc r v))
    (he : ∀ x∈ Set.Icc r v,Lives A.B.bake N (m+1) n (Q x) ∧ (Q x).beta∈band A.B.a (m+1)) : ∃ H:Spring R N m n r v Q, (H.ordinal= W.order (listIn (Q r)) ∧ H.W=W.tone) ∧ ∀ x∈ Set.Icc r v, W.sails (H.result x) (Q x):=by
  let hL : ∀ x∈ Set.Icc r v,Lives (spatial A).bake N (m+1) n (Q x) ∧ (Q x).beta∈band A.B.a (m+1):=fun x hx=> ⟨longs (he x hx).1,(he x hx).2⟩
  obtain ⟨K,-⟩:= verdict W.earns W.paid hp hL (Set.left_mem_Icc.mpr h); let v₀:=W.order (listIn (Q r))
  let V:Spring R N m n r v Q:= ⟨hp,he,K,W.tone,v₀,Classical.choice (Tree.select _ (A.B.a.clock.op m n).patch.odd_side), fun i hx=> (W.city _).emits Q K hp hL rfl i hx⟩
  exact ⟨V,⟨rfl,rfl⟩,fun x hx=> ⟨⟨Q x,hL x hx⟩,rfl,(W.at_turn K hx hp hL).2.2.symm⟩⟩
end Chord
-- next entrance HELD even with new Beacon retirement options.
open Chord FullVolume
structure Lyrics (R:Factor A) (c c₁:ℝ) where
    prim N m n:m<N→ Chord R N m n c c₁
    start (N p:ℕ) : ℝ → Rep G (A.B.a.S.side N p)
    origins (N p:ℕ) : Curve (A.B.a.budget N) (start N p) (band A.B.a N) ∧
       ∀ β ∈ band A.B.a N, let X:= start N p β; X.beta=β ∧ Lives A.B.bake N N p X ∧ A.B.bake.Starter N p X ∧ HasSlots X.p X.activities
namespace Lyrics
lemma licenses (h:Roofing R c c₁):Nonempty (Lyrics R c c₁):=by
  choose f he using Graces.hops R; exact ⟨⟨fun _ _ _ hm=> Classical.choice (Chord.acquires h hm), f,he⟩⟩
variable (V: Lyrics R c c₁)
def tunes : Recipe A.B.a:=
  { FullVolume.still R with
    next:=fun N m p r u=> (still R).next N m p r u ∧ ∃ h:m<N,(V.prim N m p h).sails r u
    first:=fun N p u=> (still R).first N p u ∧ V.start N p u.beta=u }
theorem altitude {N m p v} : Lives V.tunes N m p v↔Lives A.B.bake N m p v:= by constructor<;> rintro ⟨a,b,c,d,e'⟩<;>exact ⟨a,b,c,d,e'⟩
lemma supplier (hG:G.Simple) : V.tunes.Issues N n:=by
  constructor
  · obtain ⟨hf,h⟩:= V.origins N n
    refine ⟨V.start N n,hf,fun β hβ=>?_⟩; obtain ⟨he,hv,hr,hL⟩:= h β hβ
    exact ⟨he,(V.altitude).2 hv,hr.1,hr.2,⟨hr.inits,hL⟩,by rw [he]⟩
  intro m hm a s H Q hv hh
  obtain ⟨X,hr,hX⟩:= (V.prim N m n hm).spores a s H Q hv fun x hx=> ⟨(V.altitude).1 (hh x hx).1,(hh x hx).2⟩
  obtain ⟨hf,hF⟩:= X.moves hG hm
  refine ⟨X.result,hf,fun x hx=>?_⟩
  obtain ⟨h,hK,hp,hV⟩:= hF x hx
  exact ⟨(V.altitude).2 h.bundle,h.ident,(A.B.links hm h).drift,⟨h,⟨a,s,Q,X,x,hx,rfl,rfl⟩,by
    change |(X.result x).beta-(Q x).beta - A.B.kin.alpha N m|≤_
    unfold predictor at hK; rwa [sub_add_eq_sub_sub] at hK⟩,⟨hm,hX _ hx⟩⟩
lemma deterministic {u v} (h: Competes V.tunes n N 0 u) (h':Competes V.tunes n N 0 v) (hk : (u N).beta=(v N).beta) : m ≤ N → u m=v m:= by
  intro hm; induction hm using Nat.decreasingInduction with
  | self => exact h.fromTop.inits.2.symm.trans ((congr_arg _ hk).trans h'.fromTop.inits.2)
  | of_succ i hi ih => obtain ⟨hz,hp⟩:= (h.persists i (Nat.zero_le i) hi).continues.2; exact (V.prim N i n hi).sails_singleton (ih ▸ hp) (h'.persists i (Nat.zero_le i) hi).continues.2.choose_spec
lemma disappears {m n N u}: Competes V.tunes n N m u→ Competes (still R) n N m u := by
  intro h; refine ⟨fun i hi hx=> ⟨(FullVolume.lives R).2 ((V.altitude).1 (h.prices i hi hx).1),(h.prices i hi hx).2⟩,⟨h.fromTop.scalars,h.fromTop.raw,h.fromTop.inits.1⟩,fun i hi hx=>?_⟩
  have hf:= h.persists i hi hx; exact ⟨hf.link,hf.drift,hf.continues.1⟩
end Lyrics
end YM.PhysicalNext.Repeat.Roof
