import YM.MergeProof.East.Medal
import YM.TraceExtension.Prom.Orion.Latch
import YM.TraceExtension.Prom.Orion.Nitre
import YM.TraceExtension.Prom.Orion.Plume
import YM.TraceExtension.Prom.Orion.Suds
import YM.TraceExtension.Prom.Front.West.Lys
import YM.TraceExtension.Prom.Front.West.Tael
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Incoming
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.MergeProof.East.Medal for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ℕ→ι → Tapes.Panel D) (Z:ArcSky P)(B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels

variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
variable {x y w:ι}{c:ℝ}
-- pricing bands and purchasing

private lemma divergesTSky {x y:ℝ}(he:x<y)(c:ℝ): ∀ᶠ z in atTop, c*Perch.bill x z < Perch.bill y z:=by
   filter_upwards [Glimmer.transports he (c+1)] with i hi; refine lt_of_lt_of_le ?_ hi; exact mul_lt_mul_of_pos_right (by linarith only) (Real.exp_pos _)
private lemma caps_meSky {a b e:ℝ}(h:Checks a b e c n D)(hN : N ≤ n): Checks a b e c N D:=by
    obtain ⟨hx,he,hB,h,hA⟩:=h;have he':=(show (N:ℝ) ≤ n from Nat.cast_le.mpr hN)
    have hN(x:ℝ)(H:0≤x): x*D*N ≤ x*D*n:=by gcongr
    exact ⟨hx,he,hB,by linarith only [h,hN (a-b) (by linarith)],by linarith only [hA,hN (a-e) (by linarith)]⟩
include H hp h hZ Z
lemma aspectSky (F:Extraction.Order)(hn:2≤n)(R:ℝ)(hr:0<R)(hs:(standard C).Smooth)(H':(standard C).RealSpin)(q:ι→ℝ) (Lz:ℕ→ℝ) (hL:∀ k,0≤ Lz k) (hh:∀ k i,(P k i).arc=q i+Lz k) (g:Checks (q x) (q y) (q w) c n D)
    (t:Caps m)(ht:∀ i,t i≤D)(v:Ribbon (Bel C.book) t)(hm:m≤n)
    {f:ℕ→ℕ}(fh:Tendsto f atTop atTop)(Y:ℕ→ℕ→ℕ→TableL C D)(hY:∀ i,PoisedSky (P (f i)) B H O J n z (f i) (Y i)) :∃ e Q Q',Balances (fun i=>wok C D (f i) (P (f i) x).arc c (Y i)) F R ht v e Q Q':=by
    let a:=q x; let b:=q y;let d:=q w; let Θ k:=(P k x).arc
    have ht'(k i):=(P k i).huge
    obtain ⟨hx,hy,hz,hV,hZ'⟩:= caps_meSky g hm
    obtain ⟨X,hX⟩:= sightSky P Z B H h hp O J z hZ F hs R hn hr x c t ht v hm
    obtain ⟨e,he,hB⟩:= thirdSky P Z B H h hp O J z hZ F H' hn y Θ c (fun i=> by unfold Θ; rw [hh,hh]; linarith only [hy]) t ht v
    obtain ⟨f',he',hB'⟩:= thirdSky P Z B H h hp O J z hZ F H' hn w Θ c (fun i=> by unfold Θ; rw [hh,hh]; linarith only [hz,hx]) t ht v
    let Y' (i):= wok C D (f i) (Θ (f i)) c (Y i);let M(i):=clim A (f i);let p(i):=Perch.bill c (M i); let Q(i):=Perch.bill ((a-b)*D) (M i); let U(i):= Perch.bill ((a-d)*D) (M i); let x'(i):= e*Q i; let y'(i):=f'*U i
    have ha : 0 ≤ a-d:=by dsimp only [a,d]; linarith
    have hu(i k):0 < (P k i).arc:=by linarith only [ht' k i,Nat.cast_nonneg (α:=ℝ) D]
    have hrL : Tendsto M atTop atTop:= (hat_rate A h).comp fh
    have hσ(i): (Y' i).spacing =Perch.bill (-(Θ (f i))) (M i):=by
       rw [show _=(mag (A) (Θ (f i)) (f i))⁻¹ from wok_spacing c, mag_bill]; unfold Perch.bill;rw [mul_neg,Real.exp_neg]
    have hm:(∀ i, (Y' i).spacing ≤ Perch.bill (-a) (M i)):=by
       intro i; rw [hσ]; apply Glimmer.billed; unfold Θ a; rw [hh];linarith only [hL (f i)]
    have hT(i): (Y' i).spacing/p i≤Perch.bill (-a-c) (M i):= by
       apply (div_le_div_of_nonneg_right (hm i) (Real.exp_pos _).le).trans_eq; unfold Perch.bill; rw [← Real.exp_sub]; congr 1; ring
    have hk : -a<c:= by unfold a; have h1:=mul_nonneg (mul_nonneg ha (Nat.cast_nonneg D)) (Nat.cast_nonneg m); unfold a d at h1;linarith only [h1,hZ']
    refine ⟨fun i=>X*Ship.budget (A) n (f i),x',y',?_,?_,?_,?_,?_,?_,?_⟩
    · simpa using! ((Ship.diminishes A n h (by omega)).comp fh).const_mul X
    · exact (bill_hi hx).comp hrL
    · filter_upwards [hrL.eventually (transports hk (4*m:ℝ))] with i hi
      change _*(Y' i).spacing≤p i; exact (mul_le_mul_of_nonneg_left (hm i) (by positivity)).trans hi
    · exact Eventually.of_forall fun i=>⟨mul_nonneg he (Real.exp_pos _).le,mul_nonneg he' (Real.exp_pos _).le⟩
    · have he:= ((bill_hi hV).comp hrL).const_mul (e^m)
      rw [mul_zero] at he; exact he.congr fun j=> by
         change _ * Perch.bill _ _=(e*Q j)^m*p j; dsimp only [Q,p]; rw [mul_pow,mul_assoc (e^m), Glimmer.bills,overlap]
    · have hβ:= ((bill_hi hZ').comp hrL).const_mul (f'^m)
      rw [mul_zero] at hβ; apply squeeze_zero (g:=fun i=> f'^m* Perch.bill ((q x-q w)*D*m-q x-c) (M i)) _ _ hβ
      · intro i; change 0 ≤ y' i ^m*((Y' i).spacing/p i); rw [hσ]; exact mul_nonneg (pow_nonneg (mul_nonneg he' (Real.exp_pos _).le) _) (div_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      intro j; refine (show y' j^m*_ ≤ _ from mul_le_mul_of_nonneg_left (hT j) (pow_nonneg (mul_nonneg he' (Real.exp_pos _).le) _)).trans_eq ?_; dsimp only [y', U]; rw [mul_pow,mul_assoc (f'^m),Glimmer.bills,overlap]; dsimp only [d,a]; ring_nf
    filter_upwards [fh.eventually hX,fh.eventually hB,fh.eventually hB',fh.eventually (echo_priorSky A (m*6) h),fh.eventually (echo_scaleSky A h),hrL.eventually (divergesTSky hy (2*R)),hrL.eventually (divergesTSky hz 1)] with i h1 h2 h3 h4 h5 h6 h7
    let k:=f i; let K:= Next.Rank.Station.widthSky A (P k y).arc k;let T:=Next.Rank.Station.widthSky A (P k w).arc k
    have hv:(Y' i).r=(A).S.a k * Perch.bill (P k x).arc (M i):=by rw [← show mag A (P k x).arc k=_ from Atlas.mag_bill A (P k x).arc k];rfl
    have ha'(χ) : AllowedSky A (P k χ).arc k:= by obtain ⟨o,l,L,-⟩:= (hY i).supply χ; rw [← (P k χ).factor ((A).clock.J k) ]; exact L.age.allot.permitted
    obtain ⟨hα,hβ⟩:= h4 _ (hu _ _) (ha' y) (hY i).limit
    change (Y' i).Spots F R (X*_) (x' i) (y' i) ht v
    refine ⟨h1 (Y i) (hY i),⟨K-1,K,?_,Nat.sub_le ..,by change _< _; convert hα using 1; ring, ?_⟩, T,?_,?_⟩
    · have hf := (A).S.a_pos k
      rw [lt_div_iff₀ (by positivity : 0<2*R),hv]; change _ ≤ _ at hβ; rw [div_le_iff₀ ((A).S.a_pos _)] at hβ
      have hhV:2*R*Perch.bill ((P k y).arc+6) (M i)<Perch.bill (P k x).arc (M i):=by rw [hh k y,hh k x,add_right_comm (q y)]; rw [← overlap (q y+6), ← overlap (q x), ←mul_assoc (2*R)]; exact mul_lt_mul_of_pos_right h6 (Real.exp_pos _)
      linarith only [mul_lt_mul_of_pos_right (show 2*R*Perch.bill ((P k y).arc+6) (M i)<Perch.bill (P k x).arc (M i) from hhV) ((A).S.a_pos k), mul_le_mul_of_nonneg_left (show (A).S.a (K-1) ≤ Perch.bill ((P k y).arc+6) (M i)* (A).S.a k from hβ) (show 0≤2*R by positivity)]
    · have ht:(Θ (f i) - (P (f i) y).arc) * D=(a-b)*D:=by unfold Θ a b;rw [hh,hh];ring
      unfold x' Q; rw [← ht]; exact (h2 _ (hY i)).1
    · rw [hv]; change _ < _* _*p i; unfold p; rw [mul_assoc,overlap]; rw [one_mul] at h7
      have he := h5 _ (hu _ _) (ha' w) (hY i).limit; rw [div_le_iff₀ ((A).S.a_pos _)] at he
      have ht: Perch.bill ((P k w).arc+5) (M i) < Perch.bill ((P k x).arc+c) (M i):= by rw [hh k w,hh k x, add_right_comm (q w),add_right_comm (q x), ← overlap (q w+5),← overlap (q x+c)]; exact mul_lt_mul_of_pos_right h7 (Real.exp_pos _)
      linarith only [ (show (A).S.a T ≤ Perch.bill ((P k w).arc+5) (M i)*(A).S.a k from he),mul_lt_mul_of_pos_right ht ((A).S.a_pos k)]
    have ht:(Θ (f i) - (P (f i) w).arc) * D=(a-d)*D:=by unfold Θ a d;rw [hh,hh];ring
    unfold y' U; rw [← ht]; exact (h3 _ (hY i)).2
end YM.MergeProof.East
