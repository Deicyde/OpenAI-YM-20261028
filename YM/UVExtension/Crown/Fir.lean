import YM.UVExtension.Spire.Spark
import YM.UVExtension.Crown.Train
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Spire
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (hG:G.Simple){ε:ℝ}(t:Crest R ε)(u:Paperwork R.shape ε Camp.soft A.delay)
    (hk:Planned.Port.AtTop A.B.kin)(hp:∀ N,Start.Allows A.B.a N)(h:∀ N,Entry A.B.a N soft)(N n:ℕ)
open Cart
namespace Fitted
variable {R hG t hk hp N n} (H:Fitted R hG t hk hp N n)
    (V:Cart A.B.a N H.Hut)(he:H.Took V) {z:PlotN N}(hv:z∈Harbor N)(hZ: Cart.Light N z)
    -- omit b
local notation "a!" => A.B.a
local notation "cN" => A.B.kin.alpha N
local notation "W#"=> H.W N
variable (f: ∀ i, H.Home i)(β:ℕ→ℝ)(s:ℕ→ℝ)
structure PartsV (r:ℕ) : Prop where
    root : r≤ N
    alive i (hr:r≤ i) (hi:i≤ N): Reality A.B.a i n (H.W i) (f i) (β i)
    bare : H.race f β s N=headA R N n (β N)
    passes i (hr:r≤ i) (hi:i<N): H.race f β s i= (H.charts i hi).speck R _ (alive _ (hr.trans i.le_succ) hi) (s (i+1))

variable {f β s}{r:ℕ}(hs:PartsV H f β s r)
open UVNext.CouplingReset PhysicalNext.Repeat.Graces
include hs
lemma health (m:ℕ)(hr:r≤ m)(hm:m≤N): Lives A.B.bake N m n (H.race f β s m):= by
    induction hm using Nat.decreasingInduction with
    | self=> rw [hs.bare]; exact (sparkA R (hp _) hk (hs.alive N hs.root le_rfl).1 n|>.1) -- hp hk
    | of_succ i hi ih=> rw [hs.passes i hr hi]; exact ((H.charts i hi).voy R hG t _ _ (s (i+1)) (ih (hr.trans i.le_succ))).1.bundle
lemma season (i:ℕ)(hr:r≤ i)(hi:i<N): A.B.Move N i n (H.race f β s i) (H.race f β s (i+1)) ∧ Accurate A.B R.post N i n (H.race f β s i) (H.race f β s (i+1))∧ Protected R N i n (H.race f β s i) (H.race f β s (i+1)) := by
    rw [hs.passes i hr hi]; exact (H.charts i hi).voy R hG t _ _ (s (i+1)) (H.health hs _ (hr.trans i.le_succ) hi)
lemma rooted : Competes A.B.bake n N r (H.race f β s)∧ HasSlots (A.B.a.budget N) (H.race f β s N).activities:= by
    obtain ⟨hh,hp⟩:= (sparkA R (hp _) hk (hs.alive N hs.root le_rfl).1 n).2; constructor
    · exact ⟨fun i he hi=> ⟨H.health hs i he hi,(hs.alive i he hi).1⟩,hs.bare ▸ hh,fun i he hi=> A.B.links hi ((H.season hs i he hi).1)⟩
    rw [hs.bare]; exact hp
-- stock segment solved from normalized displacement x∈ palms, covered in calibration.
omit hs
variable (r:ℕ)(hr:r≤ N)
include he hr hv hZ
variable (b:ℝ)(hV:V.locket (A.B.a) N H.Hut r (↑b) z=z)
include hV
omit he hv hr in
private lemma plain (i)(hi:r≤ i)(hj:i≤ N): (lock R z i hj:ℂ)=↑(Camp.slope a! cN i)+((Camp.pulse a! r:ℂ)*↑b - Cart.pieces a! N H.Hut V r i z):=by
   unfold lock Dales.art; have hp:= Camp.pulse_pos A.B.a i; push_cast; let p:=Cart.node N z i hj
   have h0 : Complex.ofReal p.re=p:=by have h:= Complex.re_add_im p; rw [show p.im=0 from hZ _, Complex.ofReal_zero,zero_mul,add_zero] at h; exact h
   rw [show Complex.ofReal (Cart.node N z i hj).re=p from h0, show p= _ from congr_fun hV.symm (⟨i,Nat.lt_add_one_iff.mpr hj⟩:Fin (N+1))]
   unfold Cart.locket; dsimp only; rw [if_pos hi]; change _+(Camp.pulse A.B.a i:ℂ)*((Camp.pulse A.B.a i:ℂ)⁻¹*_) = _; rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr hp.ne')]

lemma shoots : H.PartsV (H.graceT z) (faceV (R:=R) z) (H.cash z) r:=by
   let f:=H.graceT z; let u:= faceV (R:=R) z; let p:= H.cash z
   have hF(i)(hi:i≤ N): H.graceT z i=H.file z i hi:=dif_pos hi
   have hh'(i)(hi:i≤ N): faceV (R:=R) z i=lock R z i hi:=dif_pos hi
   have hs (m:ℕ)(hi:m≤N):Reality a! m n (H.W m) (H.graceT z m) (faceV (R:=R) z m):=by rw [hF m hi,hh' m hi]; exact (H.officious V he hv hZ m hi).1
   refine ⟨hr,fun m _=> hs m,?_,fun i hj hi=>?_⟩
   · change Dales.mount R N N n _ _ (cash H z N)= _; rw [hh' _ le_rfl,hF _ le_rfl,H.entry hv,cash,dif_pos le_rfl,Nat.decreasingInduction_self]; rfl
   let J:=H.charts i hi; let t':=H.shirts i hi
   have hx := H.officious V he hv hZ (i+1) hi; let w:= Tour.royals R hG t J _ hx.1 t'
   have hS := hs (i+1) hi
   have hGx : Tour.choiceV R hG t (H.charts i hi) _ (H.shirts i hi) (H.file z (i+1) hi) (lock R z _ hi)=w:= dif_pos hx.1
   have hp : H.file z i hi.le=w:= Eq.trans (Nat.decreasingInduction_succ_left _ _ hi hi.le) hGx
   have hp' : H.graceT z i= Tour.royals R hG t J _ hS t':= by
     apply Eq.trans (hF i hi.le); simp_rw [hF (i+1) hi,hh' _ hi]; exact hp
   have hT : lock R z i hi.le= Tour.newB R J _ hx.1:= by
     have hx0:= H.plain V hZ r b hV i hj hi.le; have hx1:= H.plain V hZ r b hV _ (hj.trans i.le_succ) hi
     unfold Tour.newB; apply Complex.ofReal_injective
     rw [Complex.ofReal_add,Complex.ofReal_add, hx0, hx1, Cart.pieces, Cart.pieces, Finset.sum_range_succ,if_pos hj, H.bonusR V he hv hZ i hi]
     rw [← Camp.plus A.B.a i (α:=cN),Complex.ofReal_add]; change _=( (_+ (_-(_+ (↑(Tour.bonus R J _ hx.1):ℂ)))) +_)+_; abel
   have hm : faceV (R:=R) z i= J.newB R _ hS:= by rw [hh' i hi.le]; simp_rw [hF _ hi,hh' _ hi]; exact hT
   have hs' : H.cash z i= flatRate a! i n (H.race (H.graceT z) (faceV (R:=R) z) (H.cash z) (i+1)):= by
     unfold race; rw [hh' _ hi]; unfold cash; rw [dif_pos hi.le,dif_pos (show i+1≤N from hi)]; exact Nat.decreasingInduction_succ_left _ _ _ _
   rw [Tour.around]; change Dales.mount ..=_; exact (congr_fun (congr_arg₂ (Dales.mount R N i n) (congr_arg Subtype.val hp') hm) _).trans (congr_arg _ hs') 

end Fitted
end YM.UVExtension.Spire
