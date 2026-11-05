import YM.TraceExtension.Soot.Thrifty

/-! Generalization of `South.Sand` to arbitrary exponential kernels, with common read before stop-specific cost choices. pure.Start solo receipts. preserve arbitrary route for stress. Pay via HQ fin. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)
local notation "R"=> C.path.rep N p
variable (H:C.Makes) {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (o:∀ i:ℕ,V→Site (C.side i p))(s:V→ C.label d)(t:V→Motion)(w:ℝ) {j :ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
variable (y : Coefficient (C.labels.level d) (C.side k p))(X:Extra.Histories.Music (C.labels.level d) C.path N p) (Q d' : ℝ)
local notation "a"=> alto C.path k d
local notation "ζ!"=> ζ d
def SharpRead (u:ℝ):Prop := ∀ (B:Duet C.path (C.labels.level d) N p (C.ref d) k) (w:ℝ), Duet.Woke B C.params W (C.localSection d) w → (∀ i,B.atPoint i=0)→ 0 ≤ w → u*(F).coeffSize (B.voice k).x ≤ 4*(1+(C.path.levels.params k).columns)*w
variable (h:Scrim C W u ψ φ δ ζ r D)
include H h
lemma prevails (Q E mP:ℝ)(hE:SharpRead C N k p d (W:=W) mP)(hN:k≤N)(hM:C.ref d ≤ k)(hL: Sung Y! T N p C.params W ℓ X) (hp:∀ i:ℕ,C.ref d ≤ i→∀ hi:i<N, Carol Y! T N p i (D N p i hi) (X.tone (i+1)) (X.tone i) (ψ i))
    (hχ:y.Format 0 C.params (R k))(hφ:y.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) d')(hq:(F).coeffSize y.x + d' ≤ Q) (hc:4*(1+(C.path.levels.params k).columns)*Q ≤ E) (hx:0<Q) :
    ∃ b,mP*(F).coeffSize (y.x-(X.tone k).index b) ≤ 4*(1+(C.path.levels.params k).columns)*Q ∧ ∀ (m:ℕ)(w:ℝ), ℓ ≤ m→m≤k→0<w→w*‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2 → ∃ Z g, FReach (φ:=φ) (ζ:=ζ) (D:=D) (ψ:=ψ) C N k m p d y X Q w Z g b hN :=by
    obtain ⟨A,hA,hx',hb,hc',hq',hp',h''⟩:= antilles Y! T N p C.params W X (D N p) ψ le_rfl hM hN H.wilson hL (fun i he hx=> ⟨h.listens d N p i he (hx.trans_le hN),hp i he (hx.trans_le hN)⟩) (y) hχ hφ hq h.costs.cost h.costs.back
    let b:= (A ℓ).a; let y':= -b; let Z:= Relay.dualize T N p X ℓ k A y'; let I:= X.tone k; let v:=(Z).voice k
    refine ⟨b,?_,fun m w hK hk hw ht=>?_⟩
    · have hS : v.x=y.x-I.index b:=by refine ((hc' y').1).trans ?_; change y.x+I.index (-b)=_; rw [map_neg];rfl
      rw [← hS]; exact hE Z Q hp' (fun _=>rfl) hx.le
    have hj :∀ i:ℕ,m ≤ i→i ≤ k→ w*0 ≤ ζ d i:=fun i hp _=> (mul_zero _).le.trans (h.grows d i (hK.trans hp)).le
    have he (i) (hi:m ≤ i) (ht:i≤k): Z.cost i+(F).coeffSize (Z.voice i).x ≤ E/gainChart T k i:= (le_div_iff₀ (Real.exp_pos _)).mpr ((mul_comm ..).trans_le ((h'' i (hK.trans hi) ht).trans hc))
    let τ i:= march (fun _:Unit=>w) φ m i (); have h₀: Brine T m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    let c:=(C.path.levels.params k).columns; have hl :1 ≤ c:= (C.path.levels.params k).columns_ge; have hr:Q ≤ E:= le_trans (le_mul_of_one_le_left hx.le (show 1 ≤ 4*(1+(C.path.levels.params k).columns) by dsimp only [c] at hl; linarith only [hl])) hc
    have ht:= diet T d m φ (fun i=>ζ d i/2) w hw (fun i he=> (h₀.water i he).1) (fun i he=> le_trans (le_of_eq (b:=(φ i * ((C.S.block i).val:ℝ)^(d+1)* ζ d i)/2) (by change φ i *_*(ζ d i/2)=_; ring)) (div_le_div_of_nonneg_right (h.jump d i (hK.trans he)) (by norm_num))) k E (hx.le.trans hr) ht
    have hτ i (he:m ≤ i): 0 < τ i:= march_pos _ _ _ _ _ (fun _=>hw) h₀ i he _
    have hs(i)(hi:ℓ ≤ i)(ht:i ≤ k): (Z.voice i).Format 0 C.params (R i) ∧ (Z.voice i).remBound 0 (R i) (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (Z.cost i):= keys Y! T N p C.params X y' (hx'.chairs i hi ht) (hL.earned i hi (ht.trans hN))|>.2
    have hS : v.x=y.x-I.index b:=by refine ((hc' y').1).trans ?_; change y.x+I.index (-b)=_; rw [map_neg]; rfl
    refine ⟨Z.voice,Z.cost,⟨fun i hi=> hs i (hK.trans hi),fun i hi h₁=> (mul_le_mul_of_nonneg_left (he i hi h₁) (mul_nonneg (hτ i hi).le (norm_nonneg _))).trans ((ht i hi).trans (div_le_self (h.grows d i (hK.trans hi)|>.le) (by norm_num))),fun i hi hm=> ⟨(hx'.ships i (hK.trans hi) hm).debt y',?_⟩⟩,?_,?_,?_,?_⟩
    · obtain ⟨v,hv,hP⟩:=(hb i (hK.trans hi) hm).plays; exact ⟨v,hv,hP y'⟩
    · let l:= F; have hT:= he k hk le_rfl; rw [gainChart,sub_self,mul_zero,Real.exp_zero,div_one] at hT
      have hz: (F).coeffSize (I.index b) ≤ 2*E:=by
         have hP : I.index b=y.x - v.x:=by rw [hS]; abel
         rw [hP,sub_eq_add_neg]; apply (Size.add ..).trans; have he : (F).coeffSize (- v.x)=(F).coeffSize v.x:= by simp [Labels.Frame.coeffSize]
         rw [he]; linarith only [rem_nonneg ((hs k hM le_rfl).2),hT,hq,rem_nonneg hφ,hr]
      have hv:= ht k hk; rw [gainChart,sub_self,mul_zero,Real.exp_zero,div_one] at hv
      unfold bond; rw [map_neg,show (F).coeffSize (-I.index b)=(F).coeffSize (I.index b) from by simp [Labels.Frame.coeffSize], ← mul_assoc]; exact le_trans (mul_le_mul_of_nonneg_left hz (mul_nonneg (hτ k hk).le (norm_nonneg _))) (by linarith only [hv])
    · let t':= pair T N p X (y) d'; let b':= t'.a; let Q':=t'.sil; let I':= X.tone k; have he :=hL.earned k hM hN; have hz(w):=(he.earns w).2; have hm:=duo_exp Y! hφ (hz (-b')); let q w:=(I'.plays w).exponentialEntry 0 Y! (R k); have hQ:IsLinearMap ℂ q:=expoLinear I'.plays I'.charge he.book hz
      have hs: Z.voice k=t'.bar X y':=show (A k).bar X y'=_ from by rw [hA]
      rw [hs,show t'.bar X y'=beside Q' (I'.plays (b'+y')) from rfl, show (beside Q' (I'.plays (b'+y'))).exponentialEntry 0 Y! (R k)=_ from duo_exp Y! ((presentation hχ hφ (he.earns (-b')).1 (hz (-b'))).2) (hz (b'+y'))]; change Q'.exponentialEntry _ _ _ + q (b'+y')=_; rw [show Q'.exponentialEntry _ _ _=_ from hm]; change _ + q (-b')+q (b'+y')=_+q y'
      rw [hQ.map_add, show q (-b')= -q b' from (IsLinearMap.mk' q hQ).map_neg b']; abel
    · let t':= pair T N p X (y) d'; let b':= t'.a; let Q':=t'.sil; let I':= X.tone k; have he :=hL.earned k hM hN; have hz(w):=(he.earns w).2; have hm:=duo_profile hφ (hz (-b')); let q w:=profile (R k).activities (I'.plays w).forced; have hQ:IsLinearMap ℂ q:=inkL I'.plays I'.charge he.book hz
      have hs: Z.voice k=t'.bar X y':=show (A k).bar X y'=_ from by rw [hA]
      rw [hs,show t'.bar X y'=beside Q' (I'.plays (b'+y')) from rfl, show profile (R k).activities (beside Q' (I'.plays (b'+y'))).forced=_ from duo_profile ((presentation hχ hφ (he.earns (-b')).1 (hz (-b'))).2) (hz (b'+y'))]; change profile (R k).activities Q'.forced+q (b'+y')=_; rw [show profile (R k).activities Q'.forced =_ from hm]
      change _+q (-b')+q (b'+y')=_+q y'; rw [hQ.map_add,show q (-b')= -q b' from (IsLinearMap.mk' q hQ).map_neg b']; abel
    rw [← hS]; exact (Work.G09.cone_cost h.costs.cost h.costs.back hp' k hM le_rfl).1.trans (Work.G09.cost_finest h.costs.cost h.costs.back hp')
end YM.MergeProof.Accent
