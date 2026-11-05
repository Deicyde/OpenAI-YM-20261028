import YM.MergeProof.Marco
import YM.OPE.Columns.Strength

/-!
# Keep triangular transfer in the published factory

Strengthening of YM/MergeProof/Marco.lean; most of the proof is
the *same* construction. Adapted from that file, retaining the baseline.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Guard Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
-- interface terminalHistory selected. grants Tube. keep Grade d and potential.Cauchy.
variable (h:Nest X Y)
local notation "ℓ" => fun N p=> Keeper.sufficient (h.born N p) -- binder K Name
-- Book.T anchors
variable {Xf :∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p}{t:ℕ → ℕ}
def StackedColumns {d N p : ℕ} (T : TransferData ((Labels.frames G).level d) (Issue.trail Y) N p) (t:ℕ) (K:Bid.Worth) : Prop :=
  ∀ m, t ≤ m → m < N →
    Triangle (Issue.trail Y) K m (fun v => (T.entries (m+1) v).x) (fun v => (T.entries m v).x)
include b hG h
lemma squad_columns (t:ℕ→ℕ) (hp:∀ d,d+3≤ (Issue.trail Y).levels.clock.J (t d)): ∃ (D:∀ N p m,m<N→GaugeDoor ((H).rep N p (m+1)) ((H).rep N p m)) (Xf : ∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p),
   let F:= Family.mk H (hol G) (Labels.frames G) (localSection G) t Xf
   F.Makes ∧ Spec.Calibrated F ∧ (∀ N m p (hm:m<N), Climbs X Y N m p (D N p m hm)) ∧∀ d N p : ℕ, t d ≤ N→ Freight Y h N p d (Xf d N p) (t d) K (D N p) ∧
     StackedColumns Y (Xf d N p) (t d) K:=by
   choose D hA hD using chorus_columns hG b Y h
   -- D N p m
   let U(d):= (Labels.frames G).level d
   have he(d m) (hq : t d ≤ m):d+3 ≤ A.B.a.clock.J m:= (hp d).trans (A.B.a.fits.mono hq)
   let B(d):= localSection G d
   have hg(d N p): ∃ T: TransferData (U d) H N p, t d≤N → T.Based (hol G) (B d) (t d) ∧ Freight Y h N p d T (t d) K (D N p) ∧ StackedColumns Y T (t d) K :=by
      by_cases hx:t d≤N
      swap; · exact ⟨⟨fun _ v => Extra.Histories.primary 0 v,LinearEquiv.refl _ _⟩,fun he => False.elim (hx he)⟩
      let F:= U d; let V:= Guard.summit F (B d) H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) d; let W:= K; let S:= (B d)
      have he' := (Nat.le_add_right d 3).trans (he _ _ hx)
      have ho : OnTop S H N p (hol G) V := summon F S H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) Y.choice d (sound ..) (Doors.cameras_ge G d) (fun i=> Doors.cameras_holds G d _ i 0) ((b.clock.sequences N d he').receipts p 0)
      obtain ⟨Z,hZ,hS,hQ⟩:= MergeProof.compose_columns S H N p (hol G) W Y.choice (sound G d) b.clock.room b.clock.bank (t d) hx V ho (voice S H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) d Y.choice (sound G d) ho) (fun m hm hm'=> hD N p m hm' d (he _ _ hm))
      obtain ⟨T,hT,H'⟩:= Work.G08.answer W H b.clock.room b.clock.bank N p d (t d) _ (Z.draft H) (localSection G d) _ (Sung.clocks S H N p (hol G) K _ _ hS)
      refine ⟨T,fun _=> ⟨H',⟨Z,hZ,hT,hS,
        fun m hp hm => ⟨(hQ m hp hm).1, (hQ m hp hm).2.1⟩⟩,?_⟩⟩
      intro m he h
      rw [hT]
      have eq (i) (hv : t d ≤ i) (hu : i ≤ N) :
          (fun v => ((Z.draft H).inits i v).x) = (Z.tone i).index :=
        funext ((hS.earned i hv hu).currents)
      rw [eq m he h.le, eq (m+1) (by omega) h]
      exact (hQ m he h).2.2
   choose T hT using hg; have ha := Issue.refer H K C t b.clock hp
   refine ⟨D,T,⟨Y.choice,ha.gets,ha.order,ha.fits,?_,fun d N p hi=>(hT d N p hi).1⟩,⟨M.p,P,A.θ,A.delay,A.bar,A.asks,M.O,M.K,A.post,A.B,Y.history,Y.sticks,rfl,Y.moves⟩,fun N m p hm=>hA N p m hm,fun d N p hi=>(hT d N p hi).2⟩
   exact fun d N p hi o v=> ha.loaded d N hi _ rfl rfl _ o v
end YM.PhysicalNext.Repeat.Legato.Bandage
