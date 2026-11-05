import YM.UVExtension.Gale.Funnel
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{d:ℕ}{F:Frame G d}{A:Hol G}{s:Levels G}{n N r k:ℕ}
variable (L:∀ i:ℕ,ℂ→ Lacing.Banner s F A n i)
local notation "O'"=> s.clock
local notation "D"=> F.Coeff
local notation "H"=> Lacing.Card s F A n
local notation "X₀"=> s.params
local notation "l'"=> s.S.block
local notation "κ"=> s.clock.forcedAllowance
local notation "S"=> s.S
local notation "g₀"=> fun i=> Lacing.glaring s i n
variable (i N:ℕ)
variable (U:ℂ→ Card s F A n N)
local notation "Ψ"=> fire L N U
variable (v c q w:ℕ→ℝ)(ρ:ℕ→ℝ)
noncomputable def cotton (v w:ℕ→ℝ)(k:ℕ)(i:ℕ)(h:i≤ k) :ℝ:= Nat.decreasingInduction (motive:=fun _ _=>ℝ) (fun j _ t=>4*v j*w (j+1)*t) 2 h
lemma cottonI (i:ℕ)(hi:i<k): cotton v w k i hi.le = 4*v i*w (i+1)*cotton v w k (i+1) hi:=by unfold cotton; exact Nat.decreasingInduction_succ_left ..
lemma cotton_self : cotton v w k k le_rfl=2:=by unfold cotton; exact Nat.decreasingInduction_self ..
variable {v c q w U}{L N}{a:ℝ}(R:Rotor s F A n N r a L v c q w)(P:Booked L N U v c q w R)
local notation "Z"=>ball (0:ℂ) a
variable {z:ℂ}(hz:z∈Metric.ball 0 a) (x:F.Index)
local notation "X"=> shuttle L N U k z x
local notation "K"=> cotton v w k
include P hz
lemma levy (i)(hi:i≤k)(ht:k≤ N)(hn:r≤ i): 0≤K i hi ∧ ‖(X i hi).1.2‖≤ w i*K i hi:=by
   induction hi using Nat.decreasingInduction with
   | self=>
      rw [cotton_self,shuttles]; have hS:= (framed U R P.dims P.hulls k hn ht).1 z hz; have hw:= R.quiet k hn|>.t_now; refine ⟨zero_le_two,?_⟩
      have hp:= Gale.charge (Ψ k z) (Size.axis F x,0) (w k) 1 hw hS zero_le_one (Size.size_axis ..|>.le) (by change ‖(0:Cow G (S|>.side k n) (s.budget k) d A)‖≤1; rw [norm_zero]; norm_num)
      exact hp.trans_eq (by ring)
   | of_succ i h IH=>
      have he := h.trans_le ht; obtain ⟨T,hT,hP⟩:= R.busy i hn he; let Y:=X (i+1) h; have hv:= hT z hz; have hw:= R.quiet i hn; let w0:= w i; let w':=w (i+1); let p:= K (i+1) h
      obtain ⟨hg,hE⟩:=IH (hn.trans i.le_succ); let V:= L i z; let Q:=V.rain Y.1.2 none
      have he': 0≤ v i:=hv.counts.calm; have hx:0≤ w (i+1):=zero_le_one.trans hw.t_next
      obtain ⟨_,hp⟩:=charges V Y.1.2 hv hE ((framed U R P.dims P.hulls i hn he.le).1 z hz) hw.t_now hw.t_next hg
      rw [wheels L N U x k i h z,cottonI v w i h]; refine ⟨mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) he') hx) hg, hp.trans_eq ?_⟩; ring

-- ascend back to k, subtract.Bound ~1/4.Y_k axis. This secures inverse WITHOUT paying ∏ loop L. kinetic shift.Triangle.
lemma cape (i)(h:r≤ i)(hi:i≤ k)(ht:k≤ N):let hk:r ≤ k:= h.trans hi; let b:= (X r hk).2
   F.coeffSize (tether L N U r i h z b - (X i hi).2) ≤ K i hi/8:=by
   induction h with
   | refl=> intro hk b; rw [flipI]; change F.coeffSize (b-b)≤ _; rw [sub_self]; exact (by rw [show F.coeffSize 0=0 from by simp [Labels.Frame.coeffSize] ]; exact div_nonneg (levy R P hz x r hi ht le_rfl).1 (by norm_num))
   | step h IH=> rename_i i
                 intro hk b; have hg:= lt_of_lt_of_le (Nat.lt_succ_self i) hi; have hp:=hg.trans_le ht; have ht0:= IH hg.le; obtain ⟨T,hT,hx⟩:= R.busy i h hp
                 obtain ⟨hK,hQ⟩:= levy R P hz x (i+1) hi ht ((show r ≤ i from h).trans i.le_succ); let Y:= X (i+1) hi; let Q0:= (L i z).rain Y.1.2 none; let P':= turn L N U i z; let a:= tether L N U r i h z b; have hu: (X i hg.le).2 = P' Y.2+ Q0.1:=by rw [wheels L N U x k i hg z]; rfl
                 have hW:=R.quiet i h; have hb₀:= (charges (L i z) Y.1.2 (hT z hz) hQ ((framed U R P.dims P.hulls _ h hp.le).1 z hz) hW.t_now hW.t_next hK).1
                 rw [Gale.mirror _ _ _ _ _ h z]; change F.coeffSize (P'.symm a-Y.2) ≤ _; have heq : P'.symm a-Y.2=P'.symm (a-P' Y.2):= by rw [map_sub,P'.symm_apply_apply]
                 rw [heq]
                 have ht1:= funds U R P.dims P.hulls i h hp hz (a-P' Y.2)
                 let t:= K (i+1) hi; let d:= 2*v i*(w (i+1)*t); have hw: F.coeffSize (a - P' Y.2) ≤ K i hg.le/8+d:=by
                   rw [show a-P' Y.2=a-(X i hg.le).2+Q0.1 by rw [hu]; abel]; exact (Size.add ..).trans (add_le_add ht0 hb₀)
                 apply ht1.trans ((mul_le_mul_of_nonneg_left hw (mul_nonneg zero_le_two (zero_le_one.trans hW.calm))).trans ?_)
                 rw [cottonI v w i hg]; unfold d; have h := R.tiny i h; have hP : 2*q i*(4*v i*w (i+1)/8+ 2*v i*w (i+1)) ≤ 1/8:=by linarith only [h]
                 convert! mul_le_mul_of_nonneg_right hP (show 0≤ t from hK) using 1; · change 2*q i*(4*v i*w (i+1)*t/8+ 2*v i*(w (i+1)*t))=_; ring
                 ring
lemma bill (hk:r ≤ k)(ht:k ≤ N): F.coeffSize (tether L N U r k hk z (X r hk).2- Size.axis F x)≤1/4:=by
   have he:= cape R P hz x _ hk le_rfl ht
   dsimp only at he; rw [cotton_self,shuttles] at he; exact he.trans (by norm_num)
end YM.UVExtension.Gale
