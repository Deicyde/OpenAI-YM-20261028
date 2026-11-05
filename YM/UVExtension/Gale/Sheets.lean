import YM.UVExtension.Cloud.Desks
import YM.UVExtension.Gale.Reef
import YM.UVExtension.Cloud.Forks
import YM.UVExtension.Cloud.Skates
/-!
 # REAL spigot on the short-upper interval. No full-sequence assumptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open Fitted
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    (d N m n:ℕ)(b:Shade)
set_option quotPrecheck false
local notation "H"=> S.fits N n
local notation "V"=> S.cart N n
local notation "τ"=> S.grove.coins
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "J₀"=> A.B.a.clock.J m
local notation "J"=> A.B.a.clock.J (m+1)
local notation "Δ"=> P.L J
set_option quotPrecheck false
variable (hm:m<N)(hd:d+3≤A.B.a.clock.J m)
local notation "s"=> A.B.a
open Cloud Flake Metric Mast
variable {a:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)(he:∀ i:ℕ,∀ N:ℕ,∀ hm:i<N,∀ p:ℕ,∀ z∈Metric.ball (0:ℂ) a,Speed (pulseM A.B.a i) (ink S N i p hm.le z))
local notation "Z"=> ball (0:ℂ) a
variable (hz: Buoy X C d m)(hp':Guild.PriceS X m)
local notation "L'"=> Lacing.Banner A.B.a ((frames G).level d) (hol G) n m
local notation "t"=> C (A.B.a.clock.J (m+1))
local notation "w"=> (A.B.a.params (m+1)).columns
local notation "r"=> Doors.rate (A.B.a.S.block m)
local notation "b"=> Flake.leadF S R d N m hd
local notation "D'"=> (P.L (A.B.a.clock.J (m+1)))
include hp he hz hp' hd
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 700000 in
lemma oils (hm:m<N) :∃ L:ℂ→ L', Rains Z L∧ (∀ z∈Z, Tips (L z) (A.B.a.S.block m) b (2*r) (2*t))∧ ∀ i:Rose S,(i.val:ℂ)∈ball 0 a → L (i.val:ℂ)=tide S R d N m n i:=by
    choose Q L hX hw using fun x=> wire S R d N m n x hm hd
    obtain ⟨T,hT⟩:= sunlit S R d N m n hm hd Q L hX hp'
    let f(z:ℂ):= ink S N m n hm.le z
    have hh:MapsTo f Z spreadK.span:= fun x hx=>Cloud.upon S N m n hm (hp hx)
    have hg:DifferentiableOn ℂ f Z:= (H|>.nodded (V) (τ) m hm.le).mono hp -- notation includes V τ check
    refine ⟨T∘f,⟨?_,fun i j=> hT.stems i j _ _ Metric.isOpen_ball hh hg,fun i j=> hT.peals i j _ _ Metric.isOpen_ball hh hg,fun i j=>hT.rout ..⟩,fun z hx=> ?_,fun i hi=>?_⟩
    · intro i; cases i; simp_rw [show ∀ z:ℂ,((T∘f) z).vane none=0 from fun z=>hT.noneM (f z)]; exact differentiableOn_const _; rename_i i; exact hT.comes i _ _ Metric.isOpen_ball hh hg
    · rw [Push.PriceCompiler.block_eq A.B.valid m]; exact (rides S R d N m n hm hd Q L hX T hT hz (f z) (he m N hm n z hx)|>.1)
    obtain ⟨x,hx⟩:= yells S N m n hm i; change T (f _)= _; rw [show f (i.val:ℂ)=spreadK.call x from hx.symm,hT.key]; exact (hw x i hx).symm
-- T heading map norms independent p,b. via REAL. 
include ha n
set_option maxHeartbeats 700000 in
lemma bothEnds (hm:m<N):∀ x, (F).coeffSize ((b).map x) ≤ 2*t*(F).coeffSize x ∧ (F).coeffSize ((b).map.symm x)≤ 2*t*(F).coeffSize x:=by
    choose Q L hX hw using fun x=> wire S R d N m n x hm hd; let i:Shade:=⟨0,by norm_num [Spire.spatial, Camp.rad,Oriel.rim]⟩; have h:=tum S R d N m n i hm hd (Q i) (hX i);
    have ht:= h.2.1.wing; intro x; exact ⟨(h.1 x).1.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left ht (by norm_num)) (Work.G08.size_nonneg ..)), (h.1 x).2.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left ht (by norm_num)) (Work.G08.size_nonneg ..))⟩

omit hp' hz hd
local notation "ϕ"=> fun i=>2*Doors.rate (A.B.a.S.block i)
local notation "γ"=> fun i=>2*C (A.B.a.clock.J (i+1))
local notation "Χ"=> fun i=> (A.B.a.params i).columns
lemma pocketbook (k:ℕ)(hD: d+3 ≤ A.B.a.clock.J k)(hM:∀ i,k ≤ i→ Buoy X C d i)(hy:∀ i,k ≤ i→ Guild.PriceS X i): ∃ L:∀ m:ℕ,ℂ→ Banner A.B.a ((frames G).level d) (hol G) n m,
   Rotor s F O! n N k a L (ϕ) (γ) (γ) (Χ) ∧ (∀ i, k ≤ i → i < N→∀ z:Rose S,(z.val:ℂ)∈ Metric.ball (0:ℂ) a→ L i (z.val:ℂ)=tide S R d N i n z)∧ ∀ i≥ k, 2*γ i ≤ Χ (i+1):=by
    let H₀:= Orchard.Path S (fun _ _=> Orchard.rose0 S)
    have h(i)(hi:k≤ i):d+3 ≤ A.B.a.clock.J i:=hD.trans (A.B.a.fits.mono hi)
    have hx i (hi:k ≤ i):= holBudget (R.clock.fits H₀ rfl i d ((Nat.le_add_right d 3).trans (h i hi))) R.clock.room R.clock.bank
    have hh :∀ i:ℕ, Nonempty (Banner A.B.a (F) (hol G) n i):= fun i=>⟨tide S R d N i n (Orchard.rose0 S)⟩
    letI (i:ℕ):Nonempty (Banner A.B.a (F) (hol G) n i):= hh i
    choose! L hF ht hg using fun i h' h''=> oils S R d N i n (h i h') hp he (hM i h') (hy i h') h''
    refine ⟨L,⟨ha,fun i hi=> (hx i hi).1, fun i hi=> ?_,fun i hi hk=> ⟨leadF S R d N i (h i hi), ht i hi hk,bothEnds S R d N i n (h i hi) ha hp he (hM i hi) (hy i hi) hk⟩, hF⟩,hg,fun i hi=>?_⟩
    · have ht:= (hx i hi).2.2; let v:= C (A.B.a.clock.J (i+1)); let r' := Doors.rate (A.B.a.S.block i); let p:=(A.B.a.params (i+1)).columns; change 4096*v*r'*p ≤ 1 at ht; change 256*(2*v)*(2*r')*p ≤ _; linarith only [ht]
    have he:= (hx i hi).2.1; apply le_trans _ he; apply le_of_eq; ring
end YM.UVExtension.Gale
