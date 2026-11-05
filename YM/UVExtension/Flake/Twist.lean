import YM.UVExtension.Flake.Hulls
import YM.UVExtension.Rainfall.Yips
/-!
 # REAL spigot on the short-upper interval. No full-sequence assumptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Flake
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
local notation "Hut"=> (S.fits N n).Hut
open Camp Camp.Cart
variable (v:Rose S)
noncomputable def ink (hm:m≤N)(z:ℂ):ℂ:= node N (picked hG A.B.a N Hut (V) τ (b:=z)) m hm
local notation "Ψ" => fun (u:Rose S)=> ink S N m n hm.le (u.val:ℂ) -- quote order
include hm
lemma yells: ∃ b:Shade,(b.val:ℂ)= Ψ v:=by
   obtain ⟨p,hp,hk,-⟩:= H|>.there V (S.token N n) τ m hm.le _ v.2; refine ⟨⟨p,?_⟩,hp⟩; have hk: ‖(p:ℂ)‖ < UVExtension.Spire.spatial:= mem_ball_zero_iff.mp hk; simpa using hk
variable (he: (b.val:ℂ)=ink S N m n hm.le (v.val:ℂ))
local notation "Ps"=> lodgeX hG A.B.a N Hut V m τ
include he
lemma plumes (i:ℕ)(hi:m ≤ i)(hk:i≤N): (H).graceT (Ps b.val) i= (H).Rest V τ v.val i∧ faceV (R:=X) (Ps b.val) i= (H).Third V τ v.val i ∧ (H).cash (Ps b.val) i = (H).Sail V τ v.val i:=by
   obtain ⟨p,hp,h,hH⟩:= H|>.there V (S.token N n) τ m hm.le _ v.2; rw [show (b.val:ℂ)= (p:ℂ) from he.trans hp.symm]; exact hH i hi hk
-- Needed to allow charts on ALL real points be chosen jointly with true Φ-gates. uses deterministic Causal forward
omit he hm
private lemma hand {f f':∀ i,(S.fits N n).Home i} {x y u u':ℕ→ℝ} (hx:(H).Shot f x u) (hy:(H).Shot f' y u')(i)(hi:i<N)(h:f (i+1)=f' (i+1))(hp:x (i+1)=y (i+1)): f i=f' i ∧ x i=y i:=by
    have h0:= H|>.doors hx i hi; have h1:= H|>.doors hy i hi; constructor
    · rw [h0.2.1,h1.2.1]; simp_rw [h,hp]
    rw [h0.1,h1.1]; simp_rw [h,hp]
include hm he
lemma pigment (u:Rose S)(hx:(b.val:ℂ)=ink S N m n hm.le (u.val:ℂ)):u=v:=by
   let p:= H; let Xb(w:Rose S):= p.acts V (S.token N n) τ w.2
   obtain ⟨hy,hz,-⟩:= plumes S N m n b hm u hx m le_rfl hm.le; obtain ⟨hf,hp,-⟩:= plumes S N m n b hm v he m le_rfl hm.le
   let f:= p.Rest V τ u.val; let f':= p.Rest V τ v.val; let x:= p.Third V τ u.val; let y:= p.Third V τ v.val
   have he(i)(hi:i≤ m): f i=f' i∧x i=y i:=by
      induction hi using Nat.decreasingInduction with
      | self=>exact ⟨hy.symm.trans hf,hz.symm.trans hp⟩
      | of_succ i hi IH=> exact hand S N n (Xb u).1 (Xb v).1 i (hi.trans hm) IH.1 IH.2
   exact Subtype.ext (add_left_cancel ((Xb u).2.symm.trans ((he _ (Nat.zero_le _)).2.trans (Xb v).2)))
end YM.UVExtension.Flake
