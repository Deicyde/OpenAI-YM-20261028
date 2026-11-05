import YM.TraceExtension.Terrace.Heli
import YM.TraceExtension.Terrace.CabinBook
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes Terrace ProofPorts.GridRealModelsEstimates20261012
open PhysicalNext.Repeat.Legato.Bandage Cells Push.GridApprox YM.MergeProof.Menu
open YM.MergeProof YM.MergeProof.Accent
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}
lemma orbit_coeff (m:ℕ)(x:ℝ)(n:Side) : ∑ i∈ allotZ (G:=G) (Bay n x) m,|wage m i.2| ≤ cardB G x*wheat m:=by
    unfold allotZ Bay; rw[sum_product]; dsimp only; rw[sum_const,nsmul_eq_mul,card_product,card_univ]; refine mul_le_mul_of_nonneg_right ?_ (show 0≤ wheat m by exact sum_nonneg fun i _=>abs_nonneg _); apply Nat.cast_le.mpr; apply Nat.mul_le_mul_right; exact le_trans (Corona.halo_size ..) (by simp)
lemma tickets_pay (G:Gauge)(m:ℕ) : ∀ᶠ x:ℝ in atTop,(cardB G x*wheat m)*(peace x)⁻¹ ≤ x^2:=by
    have hf: ConstMass 0 (cardB G):=by unfold cardB; push_cast; exact ((((balloon.gather balloon).gather (mass zero_le_one)|>.crop 4).cop (mass (Nat.cast_nonneg _))))
    filter_upwards [ (((ferry hf).prod (board (show 0≤ wheat m from sum_nonneg fun i _=>abs_nonneg _))).prod fieryG) 2 (by norm_num)] with x hx;exact hx.2.trans_eq (Real.rpow_two _)
abbrev cheerC(m:ℕ):ℕ:=m
abbrev townD (x:ℝ):= 2*Terrace.coast x TileNo
variable {C:Family G}(H:C.Makes)(h:G.Simple)(θ:Terrace.PostT C.path.levels)(K:Stock.Tabs C.path.levels)
set_option quotPrecheck false
local notation "A"=>C.path.levels
local notation "T!"=> C.path
variable {r:ℕ→ℕ}{v:ℕ→ℝ}{W:∀ N p k:ℕ,k<N→GaugeDoor (C.path.rep N p (k+1)) (C.path.rep N p k)}
variable (hp:Moonlit C.path r (PhysicalNext.Repeat.Legato.Bandage.renal C.path.levels) v W)(hr:∀ᶠ i in atTop,2 ≤ r i)
def marker(m:ℕ){n:Side}(R:Rep G n)(x:ℝ)(Y:Gal G n):Config G n→ℂ:= fun U=> ↑(callX R (Shepherd.field R (Terrace.wheelQ x)) Y (peace x) m (Bay n x) U / peace x)
include hp hr h θ K H
lemma touring (m:ℕ)(hT:Terrace.auraQ C.path.levels TileNo):∀ᶠ i:ℕ in atTop,∀ p N:ℕ, let k:=Terrace.summit C.path.levels i; ∀ h:k≤N,let R:= C.path.rep N p k; let x:= (A).clock.hatBeta k; let P:=(A).params k; let Λ:= (A).clock.loopCap k; let B:=(tilesAt C.S p ((stellar A i).le.trans h));∀ (Z:ℝ)(Y:Gal G (C.side k p)), Age P x Λ R→ Garden x Λ m Z P R Y→ (∀ U, ‖marker m R x Y U‖ ≤ x^2)∧
    Interior (Push.GridApprox.window 0 (townD x)) (marker m R x Y) ∧ room C.path.levels i k (townD x) ∧ B.rootTest (C.beta N p) (backTo C.path N p h (marker m R x Y)) ≤ Terrace.Tau C.path.levels i (-1800000):=by
    let q:=Terrace.summit (A); let y(i):=(A).clock.hatBeta (q i)
    have hf:Tendsto y atTop atTop:=(hrate (A) h).comp (Sstar ..);
    filter_upwards [ trod C H h θ K hp hr TileNo hT, pegged C h θ TileNo,hf.eventually (tickets_pay G m), toll_small (x:=100000) (by norm_num) ((stickK (A) h θ).pows h 2)] with i hi he hv hx p N k hk R x P Λ B Z Y ha hY
    let n:=C.side k p; let K':= wheelQ x; let X:=tempQ x (n:=n); have hM: room C.path.levels i k (townD x):=he.1; let s:=allotZ (G:=G) (Bay n x) m; let W:=Tau C.path.levels i ; let D:= Z*peace x
    let L(e:Lip n G):= Complex.ofReal ∘ (lute R e.1 (loc e.2 * peace x) Y (Shepherd.field R K'))
    have hξ(a:Lip n G)(ht:a∈s): Interior (Push.GridApprox.window 0 (townD x)) (L a)∧ B.rootTest (C.beta N p) (backTo C.path N p hk (L a)) ≤ W (-1900000):=by
       let p':=beaconR a.1;let L':= (loomH a.1 (loc a.2 *peace x)); let f:= tailH R a.1 Y; have hH:ProofC R p'.1 f L' X D:=hY.season a ht; have ht': p'.1∈ X:=(dec_b n x).2 ((dec_b n x).1 ((mem_product.mp (mem_product.mp ht|>.1)).1)); have hQ:=tote P x Λ R ha; have hm:0∈X:=by simp[X,tempQ,tower,halo_spec];
       have hx:separation (0:Site n) p'.1 ≤ high x + 1:=by simpa [tempQ,tower,halo_spec,X] using! ht'
       rw [show L a= _ from (show L a=lensF R p'.1 p'.2 L' f K' from Wicket.tracks R a.1 (loc a.2*peace x) Y K')]; refine ⟨?_,hi p N hk ha p'.1 _ _ _ _ _ hH hQ ht' hm hx (hY.tax a ht) hY.credit⟩
       have hn:= Shepherd.panel R p'.1 p'.2 _ _ ha.good ha.coverage ha.dialect ha.high K' hH ht' _ hQ hm
       have hu : pierSize R.p K' TileNo=Terrace.coast x TileNo:=by unfold pierSize Terrace.coast;rw[ha.hM.2.1]
       rw[hu] at hn; exact hn
    let c(i:Lip n G):ℂ:=↑(wage m i.2/peace x:ℝ); let t:= marker m R x Y; let Δ:=townD x
    have hζ : t=∑ i∈ s,c i • L i:=by unfold t marker c L callX; funext U; simp[sum_div,s,mul_div_right_comm]; push_cast; refine Finset.sum_congr rfl (fun i _=>by ring)
    refine ⟨fun U=> (Complex.norm_real _).trans_le (hY.vessel U _), by change Interior _ t; rw[hζ]; exact interior_sum _ _ (fun i hi=> (hξ i hi|>.1).scale _),hM,?_⟩
    change B.rootTest (C.beta N p) (backTo C.path N p hk t) ≤ _
    have hz(i':Lip n G)(hi':i'∈s): Interior (B.chamber 0) (backTo C.path N p hk (L i')):=by
       have h0 : Interior (Push.GridApprox.window (anchor C.S p (stellar (A) i|>.le) 0) Δ) (L i'):= (show anchor C.S p (stellar (A) i|>.le) 0=0 from (C.S.toDepth _ _).root.map_zero).symm ▸ (hξ i' hi').1
       exact (backTo_local C.path N p (stellar (A) i|>.le) hk 0 Δ h0).enlarges (room_fits p (A) Δ (stellar (A) i|>.le) hk hM 0)
    rw[hζ,backTo_sum (C:=C) s N p hk (fun i=>c i • L i) (fun i hi=>show Envelope (c i • L i) from cylinder_env ((hξ i hi|>.1).scale _))];simp_rw [backTo_linear (C:=C) N p hk]
    apply (Next.UVStress.root_sum B (C.beta N p) s _ c hz (seamless H N p)).2.trans; refine le_trans (sum_le_sum (fun i hi=> mul_le_mul_of_nonneg_left ((hξ i hi).2) (norm_nonneg (c i)))) ?_; rw [← sum_mul]
    have hp:0 < peace x:= (pet x ((A).fits.delayed k|>.le) P).2.1
    have hs:(∑ i∈ s,‖c i‖) ≤ W 100000:= by
        have heq(i):‖c i‖=|wage m i.2| *(peace x)⁻¹:=(Complex.norm_real _).trans (by rw[Real.norm_eq_abs, abs_div,abs_of_pos hp]; exact div_eq_mul_inv .. )
        rw [Finset.sum_congr rfl (fun i (_:i∈s)=>heq i),← sum_mul]; exact ((mul_le_mul_of_nonneg_right (orbit_coeff (G:=G) m x n) (inv_pos.mpr hp|>.le)).trans hv).trans hx
    apply (mul_le_mul_of_nonneg_right hs (Tau_pos ..|>.le)).trans; unfold W; rw [← Tau_add];norm_num
end YM.Trace.Weir
