import YM.TraceExtension.Soot.Kid
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I : Type} [Fintype V][DecidableEq V]{B:Census V}{G:Gauge}{n:Side}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
variable {o:V→Site n}{w w':V→ℝ} {t e a b A d:ℝ}
variable {K:V→ℕ→ Config G n→ℂ}{f c:V→ℝ}{Φ X P: V→ Config G n→ℂ}{q:Config G n→ Marker.Poly B}{Y:V→ℕ→ Config G n→ℂ}
lemma pairprof (A: Activities G n)(f g:ℕ→ Config G n→ℂ)(hf:Dominated f)(hg:Dominated g): profile A (f+g)=profile A f+profile A g:=by funext i U; exact Summable.tsum_add ((hf.summable U).comp_injective Subtype.val_injective) ((hg.summable U).comp_injective Subtype.val_injective)
variable (R: RG.Rep G n)
variable {U:V→MergeProof.Response G n}
lemma cherish {m:ℕ}{δ:ℝ}(hw:∀ i,0<w i)(hp:∀ i,0<w' i)(hy:0≤a)(ha:a ≤ 1)(ht:∀ i,w i≤ a*w' i)
    (hY: Served R Φ (fun i=>profile R.activities (K i)) q o w' (R.p.supportExponent) 1)
    (hh:Occupancy o m)(he:R.activities.Valid R.p δ t)(hi:∀ i, ForceFormat R.p R.activities (o i) (K i))(H:∀ i, ForceCost R.p R.activities (K i) (f i))(hc:∀ i,w i*f i≤ e)(hε:0 ≤ e)
    (hζ:Garnish R.p o U w (R.p.supportExponent-1) b)(hb:0 ≤ b)(hU:∀ i,Dominated (Y i))
    (hδ:∀ i,profile R.activities (Y i)=hook R.activities R.p.threshold (U i)) (hf:∀ i W, coin R (X i) (Y i) W=(R.eval W:ℂ)*P i W)(hv:∀ W,R.eval W ≠ 0)(hd:0 ≤ R.p.supportExponent-4)
    (hu: let r:=m*siteFactor R.p.B; let c:= t+r*e+a+r*b; (((R.p.B+R.p.B+1)^4:ℕ):ℝ)*c ≤ 3∧Real.exp c-1 ≤ 1): Served R (Φ+X) (fun i=>profile R.activities (K i)+profile R.activities (Y i)) (couple q P) o w (R.p.supportExponent-4) 1:=by
    have hk := hY.prune hp hw (t:=0) (slighter hp hw ht hy ha) hy (by rw [add_zero] : R.p.supportExponent+0 ≤ _) (le_of_eq (mul_one a))
    have hx:= hk.jelly (L:=P); obtain ⟨F,Z,hx,hQ,hZ,hT⟩:= hx
    let Λ:= exclaim R.activities B + kilns R B K+Z; let Q(W):= Mach B (fun i=>(Φ+P) i W)+ ∑ i,F i W
    have hC : couple q P=play R B Λ Q:=hT
    obtain ⟨hb',hr⟩:= brightK R o w B K hw f hi H hh hε hc
    have hs(p): Flow o p (Λ p) R.p.threshold:= pink (pink (granular R.activities R.p B he p) (hb' p)) (hx.flag _).1
    have hR:Towed w Prod.fst Λ R.p.B (R.p.supportExponent-1) (t+m*siteFactor R.p.B*e+a) :=buoy hw (buoy hw ((vacant R.activities R.p B he w hw).shrink (sub_le_self _ (by norm_num)) le_rfl hw) hr) (hZ.shrink (sub_le_self _ (by norm_num)) le_rfl hw)
    have hI(i):Dominated (K i):= MergeProof.Float.posted (H i)
    let V'(i):=K i+Y i
    rw [hC,show (fun i=>profile R.activities (K i)+profile R.activities (Y i))= _ from funext fun i=>(pairprof R.activities _ _ (hI i) (hU i)).symm]; let d:= R.p.supportExponent-4
    apply closeup R U Λ Q hζ hs _ he (S:=a) _ _ hw hb hh (fun p=>(hx.exp p).1) (hQ.shrink (by linarith : d+0≤_) le_rfl hw) hR (z:=3) (by unfold d; ring) (by unfold d;rwa[add_zero]) (by exact_mod_cast hu.1) hw (μ:=0) (show Repegs o R.p.B w w 0 1 B from by simp[Repegs]) zero_le_one (by rwa[one_mul]) (by rw[one_mul];exact hu.2) (fun i j W=> ?_) ?_ (fun i=> MergeProof.Float.combn (hI i) (hU i)) hv
    -- solve goals order
    · intro i W; unfold Λ; simp_rw[Pi.add_apply, Poly.part_plus, hop B _ ((hx.flag _).2 W),exclaim,kilns,mute, add_zero]; simp [bar,Poly.bead]
    · intro W; unfold Q;rw [Poly.part_plus, mute,Poly.part_sum,sum_eq_zero (fun i _=>(hx.exp _).1.sil _), add_zero]
    · intro W z hz; rw [show Q W=_ from rfl];unfold Q; rw [Poly.part_plus, hush _ _ hz,zero_add]
    swap
    · unfold Λ; rw [pairprof R.activities _ _ (hI _) (hU _), hδ]; simp_rw [Pi.add_apply,exclaim,kilns,Poly.part_plus,sing,hop₁ _ _ ((hx.flag i).2 W),add_zero]; simp [bar, Poly.bead,B.fire_hot]
    intro i V; rw [← hC]; let y:= q V; obtain ⟨h,h'⟩:= hY.relay hI he V
    rw [couple,shock,whisper _ _ (mute ..), h,h', Poly.pass_part _ (mute ..),sing,mul_one]; change _= coin R (_ + _) (_ + _) V; rw [MergeProof.Float.coin_plus R _ _ (hI _) (hU _) he.boundK]; simp_rw [Pi.add_apply,hf,add_comm]
end YM.MergeProof.Accent
