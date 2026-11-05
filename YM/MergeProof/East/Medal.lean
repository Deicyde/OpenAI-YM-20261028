import YM.MergeProof.East.Latch
import YM.MergeProof.East.Nitre
import YM.MergeProof.East.Suds

/-! # Triad of calibrations.Marks.clasp -/
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
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
variable {x y w:ι}{c:ℝ}
-- pricing bands and purchasing
structure Checks (a b e c:ℝ)(n D:ℕ):Prop where
    negative : c<0
    boundA : b+6<a
    boundB : e+5<a+c
    limitA : (a-b)*D*n+c<0
    limitB : (a-e)*D*n - a-c < 0
private lemma divergesT {x y:ℝ}(he:x<y)(c:ℝ): ∀ᶠ z in atTop, c*Perch.bill x z < Perch.bill y z:=by
   filter_upwards [Glimmer.transports he (c+1)] with i hi; refine lt_of_lt_of_le ?_ hi; exact mul_lt_mul_of_pos_right (by linarith only) (Real.exp_pos _)
private lemma caps_me (h:Checks (P x).arc (P y).arc (P w).arc c n D)(hN : N ≤ n): Checks (P x).arc (P y).arc (P w).arc c N D:=by
    obtain ⟨hx,he,hB,h,hA⟩:=h;have he':=(show (N:ℝ) ≤ n from Nat.cast_le.mpr hN)
    have hN(x:ℝ)(H:0≤x): x*D*N ≤ x*D*n:=by gcongr
    exact ⟨hx,he,hB,by linarith only [h,hN ((P x).arc-(P y).arc) (by linarith)],by linarith only [hA,hN ((P x).arc-(P w).arc) (by linarith)]⟩
include H hp h hZ
lemma aspect (F:Extraction.Order)(hn:2≤n)(R:ℝ)(hr:0<R)(hs:(S).Smooth)(H':(S).RealSpin)(g:Checks (P x).arc (P y).arc (P w).arc c n D)
    (t:Caps m)(ht:∀ i,t i≤D)(v:Ribbon (Bel C.book) t)(hm:m≤n)
    {f:ℕ→ℕ}(fh:Tendsto f atTop atTop)(Y:ℕ→ℕ→ℕ→TableL C D)(hY:∀ i,Poised P B H O J n z (f i) (Y i)) :∃ e Q Q',Balances (fun i=>wok C D (f i) (P x).arc c (Y i)) F R ht v e Q Q':=by
    let a:=(P x).arc; let b:=(P y).arc;let d:=(P w).arc
    obtain ⟨hx,hy,hz,hV,hZ'⟩:= caps_me P g hm
    obtain ⟨X,hX⟩:= sight P B H h hp O J z hZ F hs R hn hr x c t ht v hm
    obtain ⟨e,he,hB⟩:= third P B H h hp O J z hZ F H' hn y a c (by unfold a; linarith only [hy]) t ht v
    obtain ⟨f',he',hB'⟩:= third P B H h hp O J z hZ F H' hn w a c (by unfold a; linarith only [hz,hx]) t ht v
    let Y' (i):= wok C D (f i) a c (Y i);let M(i):=clim A (f i);let p(i):=Perch.bill c (M i); let Q(i):=Perch.bill ((a-b)*D) (M i); let U(i):= Perch.bill ((a-d)*D) (M i); let x'(i):= e*Q i; let y'(i):=f'*U i
    have ha : 0 ≤ a-d:=by dsimp only [a,d]; linarith
    have hu(i):0 < (P i).arc:=by linarith only [(P i).huge,Nat.cast_nonneg (α:=ℝ) D]
    have hL : Tendsto M atTop atTop:= (hat_rate A h).comp fh
    have hσ(i): (Y' i).spacing =Perch.bill (-a) (M i):=by
       rw [show _=(mag (A) a (f i))⁻¹ from wok_spacing c, mag_bill]; unfold Perch.bill;rw [mul_neg,Real.exp_neg]
    have hT(i): (Y' i).spacing/p i=Perch.bill (-a-c) (M i):=by rw [hσ]; unfold p Perch.bill; rw [← Real.exp_sub]; congr 1; ring
    have hk : -a<c:= by unfold a; have h1:=mul_nonneg (mul_nonneg ha (Nat.cast_nonneg D)) (Nat.cast_nonneg m); unfold a d at h1;linarith only [h1,hZ']
    refine ⟨fun i=>X*Ship.budget (A) n (f i),x',y',?_,?_,?_,?_,?_,?_,?_⟩
    · simpa using! ((Ship.diminishes A n h (by omega)).comp fh).const_mul X
    · exact (bill_hi hx).comp hL
    · filter_upwards [hL.eventually (transports hk (4*m:ℝ))] with i hi
      change _*(Y' i).spacing≤p i; rw [hσ]; exact hi
    · exact Eventually.of_forall fun i=>⟨mul_nonneg he (Real.exp_pos _).le,mul_nonneg he' (Real.exp_pos _).le⟩
    · have he:= ((bill_hi hV).comp hL).const_mul (e^m)
      rw [mul_zero] at he; exact he.congr fun j=> by
         change _ * Perch.bill _ _=(e*Q j)^m*p j; dsimp only [Q,p]; rw [mul_pow,mul_assoc (e^m), Glimmer.bills,overlap]
    · have he:= ((bill_hi hZ').comp hL).const_mul (f'^m)
      rw [mul_zero] at he; exact he.congr fun j =>by
         change _ * Perch.bill _ _=(f'*U j)^m*((Y' j).spacing / p j);rw [hT]; dsimp only [U]; rw [mul_pow,mul_assoc (f'^m),Glimmer.bills,overlap]; dsimp only [d,a]; ring_nf -- maybe
    filter_upwards [fh.eventually hX,fh.eventually hB,fh.eventually hB',fh.eventually (echo_prior A b (m*6) (hu y) h),fh.eventually (echo_scale A h d (hu w)),hL.eventually (divergesT hy (2*R)),hL.eventually (divergesT hz 1)] with i h1 h2 h3 h4 h5 h6 h7
    let k:=f i; let K:= Next.Rank.Station.width A b k;let T:=Next.Rank.Station.width A d k
    have hv:(Y' i).r=(A).S.a k * Perch.bill a (M i):=by rw [← show mag A a k=_ from Atlas.mag_bill A a k];rfl
    have ha'(χ) : Allowed A (P χ).arc k:= by obtain ⟨o,l,L,-⟩:= (hY i).supply χ; rw [← (P χ).factor ((A).clock.J k) ]; exact L.age.allot.permitted
    obtain ⟨hα,hβ⟩:= h4 (ha' _) (hY i).limit
    change (Y' i).Spots F R (X*_) (x' i) (y' i) ht v
    refine ⟨h1 (Y i) (hY i),⟨K-1,K,?_,Nat.sub_le ..,by change _< _; convert hα using 1; ring, (h2 _ (hY i)).1⟩, T,?_,(h3 _ (hY i)).2⟩
    · have hf := (A).S.a_pos k
      rw [lt_div_iff₀ (by positivity : 0<2*R),hv]; change _ ≤ _ at hβ; rw [div_le_iff₀ ((A).S.a_pos _)] at hβ
      linarith only [mul_lt_mul_of_pos_right (show 2*R*Perch.bill (b+6) (M i)<Perch.bill a (M i) from h6) ((A).S.a_pos k), mul_le_mul_of_nonneg_left (show (A).S.a (K-1) ≤ Perch.bill (b+6) (M i)* (A).S.a k from hβ) (show 0≤2*R by positivity)]
    rw [hv]; change _ < _* _*p i; unfold p; rw [mul_assoc,overlap]; rw [one_mul] at h7
    have he := h5 (ha' _) (hY i).limit; rw [div_le_iff₀ ((A).S.a_pos _)] at he
    linarith only [ (show (A).S.a T ≤ Perch.bill (d+5) (M i)*(A).S.a k from he),mul_lt_mul_of_pos_right (show Perch.bill (d+5) (M i) < Perch.bill (a+c) (M i) from h7) ((A).S.a_pos k)]
end YM.MergeProof.East
