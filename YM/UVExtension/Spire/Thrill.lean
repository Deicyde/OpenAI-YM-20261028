import YM.UVExtension.Spire.Count
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
    {b:ℝ}
local notation "a!" => A.B.a
local notation "cN" => A.B.kin.alpha N
local notation "W#"=> H.W N
variable (f: ∀ i, H.Home i)(β:ℕ→ℝ)(s:ℕ→ℝ)
-- Repository success prescription. Can make this proposition without chart coordinates;
-- these are bookkeeping for the reps. Path, Gauge, all intermediate payments not tilted.
def race : Trail A.B.a n:= fun i=> mount R N i n (f i).val (β i) (s i)
structure Shot : Prop where
    alive i (hi:i≤N): Reality A.B.a i n (H.W i) (f i) (β i)
    bare : H.race f β s N=headA R N n (β N)
    passes i (hi:i<N): H.race f β s i= (H.charts i hi).speck R _ (alive _ hi) (s (i+1))

variable {f β s}(hs:Shot H f β s)
open UVNext.CouplingReset PhysicalNext.Repeat.Graces
include hs
lemma sample (m:ℕ)(hm:m≤N): Lives A.B.bake N m n (H.race f β s m):= by
    induction hm using Nat.decreasingInduction with
    | self=> rw [hs.bare]; exact (sparkA R (hp _) hk (hs.alive N le_rfl).1 n|>.1) -- hp hk
    | of_succ i hi ih=> rw [hs.passes i hi]; exact ((H.charts i hi).voy R hG t _ _ (s (i+1)) ih).1.bundle
lemma serves (i:ℕ)(hi:i<N): A.B.Move N i n (H.race f β s i) (H.race f β s (i+1)) ∧ Accurate A.B R.post N i n (H.race f β s i) (H.race f β s (i+1))∧ Protected R N i n (H.race f β s i) (H.race f β s (i+1)) := by
    rw [hs.passes i hi]; exact (H.charts i hi).voy R hG t _ _ (s (i+1)) (H.sample hs _ hi)
lemma round : Competes A.B.bake n N 0 (H.race f β s)∧ HasSlots (A.B.a.budget N) (H.race f β s N).activities:= by
    obtain ⟨hh,hp⟩:= (sparkA R (hp _) hk (hs.alive N le_rfl).1 n).2; constructor
    · exact ⟨fun i _ hi=> ⟨H.sample hs i hi,(hs.alive i hi).1⟩,hs.bare ▸ hh,fun i _ hi=> A.B.links hi ((H.serves hs i hi).1)⟩
    rw [hs.bare]; exact hp
lemma doors (i:ℕ)(hi:i<N):
    β i=(H.charts i hi).newB R _ (hs.alive _ hi) ∧ f i=(H.charts i hi).royals R hG t _ (hs.alive _ hi) (H.shirts i hi) ∧ s i = flatRate A.B.a i n (H.race f β s (i+1)):= by
    have h:= (hs.passes i hi).trans ((H.charts i hi).around ..); exact ⟨congr_arg RG.Rep.beta h, Subtype.ext (congr_arg (fun x=> (x.activities.E,x.activities.K)) h), congr_arg RG.Rep.v h⟩
omit hs
include hv he hZ

def faceV (z:PlotN N)(i:ℕ):= if h:i≤N then lock R z i h else 0
-- need factor param
def graceT (z:PlotN N)(i:ℕ): H.Home i:= if h:i≤N then H.file z i h else 0

def cash (z:PlotN N)(i:ℕ):ℝ:= if h:i≤ N then Nat.decreasingInduction (motive:=fun _ _=>ℝ) (fun m hm s=>flatRate a! m n (mount R N (m+1) n (graceT H z (m+1)).val (lock R z (m+1) hm) s)) 0 h else 0

-- solves real equations; via coordinate equality (therefore no derivative bias).
variable (hh:Cart.veil A.B.a N H.Hut V (↑b) z=z)
include hh
omit he hv in
lemma fixedRow (i)(hi:i≤N): (lock R z i hi:ℂ)=↑(Camp.slope a! cN i)+(↑b -∑ j∈Finset.range i,V.tally a! N H.Hut z j):=by
   unfold lock Dales.art
   have hp:= Camp.pulse_pos A.B.a i; push_cast
   let p:=Cart.node N z i hi
   have h0 : Complex.ofReal p.re=p:=by have h:= Complex.re_add_im p; rw [show p.im=0 from hZ _, Complex.ofReal_zero,zero_mul,add_zero] at h; exact h
   rw [show Complex.ofReal (Cart.node N z i hi).re=p from h0, show p= _ from congr_fun hh.symm (⟨i,Nat.lt_add_one_iff.mpr hi⟩:Fin (N+1))]; unfold Cart.veil; dsimp only; change _+(Camp.pulse A.B.a i:ℂ)*((Camp.pulse A.B.a i:ℂ)⁻¹*_) = _; rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr hp.ne')]
lemma stock : H.Shot (H.graceT z) (faceV (R:=R) z) (H.cash z)∧ faceV (R:=R) z 0=A.B.a.clock.bar+b:=by
   let f:=H.graceT z; let u:= faceV (R:=R) z; let p:= H.cash z
   have hF(i)(hi:i≤N): H.graceT z i=H.file z i hi:=dif_pos hi
   have hh'(i)(hi:i≤N): faceV (R:=R) z i=lock R z i hi:=dif_pos hi
   have hs (m:ℕ)(hi:m≤N):Reality a! m n (H.W m) (H.graceT z m) (faceV (R:=R) z m):=by rw [hF m hi,hh' m hi]; exact (H.officious V he hv hZ m hi).1
   constructor
   · refine ⟨hs,?_, fun i hi=> ?_⟩
     · change Dales.mount R N N n _ _ (cash H z N)= _; rw [hh' _ le_rfl,hF _ le_rfl,H.entry hv,cash,dif_pos le_rfl,Nat.decreasingInduction_self]; rfl
     let J:=H.charts i hi; let t':=H.shirts i hi
     have hx := H.officious V he hv hZ (i+1) hi; let w:= Tour.royals R hG t J _ hx.1 t'
     have hS := hs (i+1) hi
     have hGx : Tour.choiceV R hG t (H.charts i hi) _ (H.shirts i hi) (H.file z (i+1) hi) (lock R z _ hi)=w:= dif_pos hx.1
     have hp : H.file z i hi.le=w:= Eq.trans (Nat.decreasingInduction_succ_left _ _ hi hi.le) hGx
     have hp' : H.graceT z i= Tour.royals R hG t J _ hS t':= by
       apply Eq.trans (hF i hi.le); simp_rw [hF (i+1) hi,hh' _ hi]; exact hp
     have hT : lock R z i hi.le= Tour.newB R J _ hx.1:= by
       have hx0:= H.fixedRow V hZ hh i hi.le; have hx1:= H.fixedRow V hZ hh _ hi
       unfold Tour.newB; apply Complex.ofReal_injective
       rw [Complex.ofReal_add,Complex.ofReal_add, hx0, hx1, Finset.sum_range_succ, H.bonusR V he hv hZ i hi]
       rw [← Camp.plus A.B.a i (α:=cN),Complex.ofReal_add]; change _=( (_+ (_-(_+ (↑(Tour.bonus R J _ hx.1):ℂ)))) +_)+_; abel
     have hm : faceV (R:=R) z i= J.newB R _ hS:= by rw [hh' i hi.le]; simp_rw [hF _ hi,hh' _ hi]; exact hT
     have hs' : H.cash z i= flatRate a! i n (H.race (H.graceT z) (faceV (R:=R) z) (H.cash z) (i+1)):= by
       unfold race; rw [hh' _ hi]; unfold cash; rw [dif_pos hi.le,dif_pos (show i+1≤N from hi)]; exact Nat.decreasingInduction_succ_left _ _ _ _
     rw [Tour.around]; change Dales.mount ..=_; exact (congr_fun (congr_arg₂ (Dales.mount R N i n) (congr_arg Subtype.val hp') hm) _).trans (congr_arg _ hs') 
   rw [hh' _ (Nat.zero_le _)]
   apply Complex.ofReal_injective
   rw [Complex.ofReal_add]; exact (H.fixedRow V hZ hh 0 (Nat.zero_le _)).trans (by simp [Camp.first])
end Fitted
end YM.UVExtension.Spire
#print axioms YM.UVExtension.Spire.Fitted.stock
