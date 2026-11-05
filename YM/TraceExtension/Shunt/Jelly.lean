import YM.TraceExtension.Shunt.Glyph
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shunt
open RG Wilson Lattice Source Labels Finset Push.Local Next.Foundations MergeProof Planned.GuardedAtom Guard Extra.Histories Filter Function Relay
open MeasureTheory
open Pressure Stationary AnalyticBridge VerifiedReset Perfect Turret Shepherd Filch Fen Kits Pills Loft Xo Zn Swift Wicket Weir Push.Uniform StressFlux Det
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side} {T:SectionData F}{H:Hol G}{R:Rep G n}{x v w p c k u a:ℝ} {J: Dart G n}{A:Stage}
abbrev filmR (f:Peat G n):Film G n:= Complex.ofRealCLM ∘ f
lemma Real_regular {f: Peat G n} {P:Support n}(h:R.p.Regular P f): R.p.Regular P (filmR f):=by
    let L:= Complex.ofRealCLM; have hf(U)(hz:Healthy R.p.threshold P U):Push.Local.Chart R.p.order (L ∘ f) U:= L.contDiff.contDiffAt.comp _ (h.smooth U hz); exact ⟨fun u v he=> congr_arg L (h.sites _ _ he),L.continuous.measurable.comp h.borel,fun v U=>congr_arg L (h.symmetry _ _),hf,fun u hv A _ hl=> left_has A hl (hf _ hv)⟩
lemma Real_salary {f:Peat G n} {P:Support n}(h:R.p.Regular P f)(he:R.p.supBounds (0:Site n) P f c) : R.p.supBounds 0 P (filmR f) c:=by
    refine ⟨he.1,fun U H l hl hh=> ?_⟩; unfold filmR; rw [left_linear Complex.ofRealCLM l (h.smooth U H) hl]; exact (Complex.norm_real _).trans_le (he.2 U H l hl hh)
-- atlas.Day.Finite FD Split up to clock.R.
def altoD (R:Rep G n)(x:ℝ)(H:Hol G)(F:Labels.Frame G 5) (f:Peat G n):= Push.Local.weighted H F (0:Site n) (tempQ x) R.p.threshold (filmR f)
abbrev addUp(R:Rep G n)(x:ℝ)(J:Dart G n)(m q:ℕ)(A: Finset GreenA)(Q L: Finset ℕ)(H:Hol G)(F:Labels.Frame G 5)(b:Axis):F.Coeff:= ∑ i ∈ stemsM R (shelves n A Q L) x m q, Push.Local.weighted H F 0 (tileZ R x i) R.p.threshold (filmR (rotateK R x m J b A Q i))
abbrev Fused(R:Rep G n)(x:ℝ)(J:Dart G n)(m:ℕ)(P:Finset GreenA)(Q:Finset ℕ)(H: Hol G)(F:Labels.Frame G 5)(b:Axis): F.Coeff:= altoD R x H F (relic R J x P b)+altoD R x H F (Xo.stubJ (lush (YCore x J b)))-altoD R x H F (rimW R Q x (YCore x J) b)+altoD R x H F (Weir.kerr x m (YCore x J b) (ochre R x P Q))
variable {G:Gauge}{F:Labels.Frame G 5}{n:Side}{T:SectionData F}{H:Hol G}{R:Rep G n}{v w m:ℕ}{Y:Gal G n}{S:Stage}{x c:ℝ}{J:Dart G n}
abbrev tuneD(A:Finset GreenA)(Q L:Finset ℕ)(x:ℝ)(R:Rep G n)(J:Dart G n)(m q:ℕ)(H:Hol G)(F:Labels.Frame G 5)(b:Axis):F.Coeff:= Fused R x J m A Q H F b + addUp R x J m q A Q L H F b
-- Film atlas.Sum.Core.
private lemma pension {d:ℕ}(X Y K Z:Film G n)(t:ℝ)(P:Support n)(B:BudgetPoint)(F: Labels.Frame G d)(hX:B.Regular P X)(hY:B.Regular P Y)(hK:B.Regular P K)(hZ:B.Regular P Z)(h : d ≤ B.order) : weighted H F 0 P t (X+Y-K+Z) = weighted H F 0 P t X+weighted H F 0 P t Y-weighted H F 0 P t K+weighted H F 0 P t Z:=by
    unfold Push.Local.weighted; rw [project_add H 0 (regular_sub (regular_add hX hY) hK) hZ h]; rw [show Push.Local.project H 0 P (X+Y-K) d =Push.Local.project H 0 P (X+Y) d-Push.Local.project H 0 P K d from (by apply eq_sub_of_add_eq; rw [←project_add H 0 (regular_sub (regular_add hX hY) hK) hK h]; rw [sub_add_cancel]), project_add H 0 hX hY h]; simp only [map_add,map_sub]
lemma tintX {q:Peat G n} {A:Support n}(hp:R.p.Regular A (filmR q))(k:ℝ): filmR (k • q)= (k:ℂ) • filmR q:=by ext1 i; push_cast; simp[filmR]
lemma plush (Z:Support n)(P Q:Peat G n)(R:Rep G n) (k:ℝ):
    filmR (P+Q)=filmR P+filmR Q ∧ filmR (-P)= -filmR P ∧ filmR (P-Q)=filmR P - filmR Q:=by refine ⟨funext (fun U=>?_),funext (fun U=>?_),funext (fun U=>?_)⟩; all_goals simp[filmR]
lemma duetM (c:ℝ)(k β q:ℕ)(x Λ:ℝ)(A: Finset GreenA)(Q L:Finset ℕ)(b:Axis) (R:Rep G n)(hm:ToolF k q (Cleft x q) x (peace x) R)(ht:Readable H T R.p n c)(hT:T.footprint (0:Site n)⊆tempQ x)(hx:Age S x Λ R) (hM: Merch R x J A Q k)(hY:Wealth S R x J)(hp:Depot R x (shelves n A Q L) q k (YCore x J b) (ochre R x A Q) (swole x)) :
    let r:= readPrice H F; let h:= atomPrice H F c; let c₁:= 2*crumb x+2*trayF x; let c₁':=R.p.mass (tempQ x (n:=n)) c₁+swole x
    ∃ X:Coefficient F n, Proxy T H R (tower (Cleft x q)) X (filmR (composedZ R x J k q A Q L b)) (smoke x) (c₁' *(r+h)) (c₁'*((1+c)*r+h)) ∧ X.x=tuneD A Q L x R J k q H F b ∧ F.coeffSize (addUp R x J k q A Q L H F b) ≤(r+h)* swole x:=by
   intro r u c' U; let p:=tempQ x (n:=n); let X:= tower (Cleft x q) (n:=n); let v:= YCore x J b; let K:=shelves n A Q L; let B:=R.p; let f(i:Tides n G):= rotateK R x k J b A Q i
   let Y:=stemsM R K x k q; let s:= Fused R x J k A Q H F b
   obtain ⟨g,hg,hG⟩:=hp.bill; let h(i:Tides n G):= |teas i k/peace x| *g i;
   let S(i:Tides n G):= tileZ R x i; let z(i:Tides n G):=secondary T H R (S i) (filmR (f i)); let o(i:Tides n G):=B.mass (S i) (h i)
   have hv:0<smoke x:=Real.exp_pos _
   have hH(i:Tides n G)(hi:i∈ Y): S i ⊆ X :=by
       apply union_subset hm.tree; intro j hj; obtain ⟨l,hL,hx⟩:=mem_biUnion.mp hj; have ht: i.2⊆ closeT R x i.1.1 K q:=mem_powerset.mp (mem_of_mem_erase ((sting ..).1 hi).2); obtain ⟨hp,hq,hF⟩:= (show Below R (beaconR i.1.1) (rim x) q (closeT R x i.1.1 K q) from flair R K q _ _) l (ht hL); exact (hm.array _ ((sting ..).1 hi).1 l hp hq) hx
   have hv(i:Tides n G)(hi:i∈Y): B.Regular (S i) (filmR (f i))∧ B.supBounds (0:Site n) (S i) (filmR (f i)) (h i):=by
       let j:= (teas i k/peace x); let W:= radarT R v (ochre R x A Q) (peace x) i; obtain ⟨hb,h₁⟩:=hG i hi
       have h' :R.p.Regular (S i) (filmR W):= Real_regular hb; rw[show filmR (f i)=(j:ℂ) • filmR W from tintX h' j]
       refine ⟨regular_smul _ h',?_⟩; change B.supBounds 0 (S i) ((j:ℂ) • filmR W) (‖j‖ * g i); rw[← Complex.norm_real j]
       exact bound_smul (j:ℂ) (Real_salary hb h₁)
   let r':=r+u; let s':=(1+c)*r+u; have hr:r≤r':=le_add_of_nonneg_right (zero_le_one.trans (atomPrice_ge_one H F ht.nonneg)); have ht' :1 ≤r:= readPrice_pos ..; have hu: 0≤ s':= add_nonneg (by positivity[ht.nonneg]) (zero_le_one.trans (atomPrice_ge_one H F ht.nonneg));
   have hp(i:Tides n G)(hi:i∈Y):Proxy T H R X (z i) (filmR (f i)) (smoke x) (o i*r') (o i*s'):= (blue_price ht (hT.trans (subset_union_left)) (hv i hi).1 (hv i hi).2 ‹0< smoke x›).wide le_rfl le_rfl (hH i hi)
   have hx': ∑ i∈Y,o i ≤ swole x:=by
       apply le_trans _ hg; refine le_of_eq (Finset.sum_congr rfl (fun i hi=> ?_)); unfold o BudgetPoint.mass h; exact mul_left_comm ..

   have hD:F.coeffSize (addUp R x J k q A Q L H F b) ≤ r'*swole x:=by
       have hz(L:Finset (Tides n G))(he:L⊆Y): F.coeffSize (∑ i∈ L,(z i).x) ≤ (∑ i∈L, o i*r'):=by
           induction L using Finset.induction with
           | empty=> simp [Frame.coeffSize]
           | insert i L h hi=>
              rw [sum_insert h,sum_insert h]; apply (Size.add ..).trans; have hv:= hi ((subset_insert _ _).trans he); obtain ⟨a,h₁,hA⟩:= (hp i (he (mem_insert_self ..))).charge; exact add_le_add ((le_add_of_nonneg_right (rem_nonneg hA)).trans h₁) hv
       apply (hz Y (fun _ h=>h)).trans; rw [← sum_mul,mul_comm r']; exact mul_le_mul_of_nonneg_right hx' (zero_le_one.trans (ht'.trans hr))
   let X0:= relic R J x A b; let X1:= Xo.stubJ (lush v); let X2:= rimW R Q x (YCore x J) b; let X3:= Weir.kerr x k v (ochre R x A Q); let G':= filmR (altF R x J k A Q b)
   have hm' : G'= filmR X0+filmR X1-filmR X2+filmR X3:= (plush p _ X3 R 0).1.trans (congr_arg₂ (·+·) ((plush p _ X2 R 0).2.2.trans (congr_arg₂ (·-·) (plush p X0 X1 R 0|>.1) rfl)) rfl)
   have hp₀:=Real_regular (hM.relicC b).regular; have hp₁:= Real_regular (hY.mids b).puff.regular; have hp₂:= Real_regular (hM.loop b).puff.regular; have hp₃:= Real_regular (hM.tune b).regular; let V:= secondary T H R p G'
   have hZ : B.Regular p G':= hm'.symm ▸ regular_add (regular_sub (regular_add hp₀ hp₁) hp₂) hp₃
   have hT : B.supBounds (0:Site n) p G' c':=by
       rw[hm']; rw [show c'= ((crumb x+trayF x)+trayF x)+crumb x from (by unfold c';ring)]; exact bound_add (regular_sub (regular_add hp₀ hp₁) hp₂) hp₃ (bound_sub (regular_add hp₀ hp₁) hp₂ (bound_add hp₀ hp₁ (Real_salary (hM.relicC b).regular (hM.relicC b).fare) (Real_salary (hY.mids b).puff.regular (hY.mids b).puff.fare)) (Real_salary (hM.loop b).puff.regular (hM.loop b).puff.fare)) (Real_salary (hM.tune b).regular (hM.tune b).fare)
   have hV : V.x= s:=by
       change Push.Local.weighted H F 0 p R.p.threshold G' =_; rw [hm']; apply pension _ _ _ _ _ _ _ _ hp₀ hp₁ hp₂ hp₃ ht.order
   obtain ⟨S₁,h₁,h₂⟩:= Proxy.summed Y z (fun i=>filmR (f i)) (fun i=>o i*r') (fun i=>o i*s') (((blue_price ht ‹_› hZ hT ‹_›) : Proxy T H R p V G' (smoke x) (R.p.mass p c'*r') (R.p.mass p c'*s')).wide le_rfl le_rfl hm.tree) hp
   have he : (∑ i∈Y,filmR (f i))+G'= filmR (composedZ R x J k q A Q L b):=by funext u; unfold composedZ filmR; simp only[filmR, Function.comp_apply, Pi.add_apply, map_add, map_sum, Finset.sum_apply, G']; unfold Y K f; rw[add_comm]
   refine ⟨S₁,he ▸ (h₁.wide ?_ ?_ (fun _ h=>h)),?_,hD ⟩
   · rw [← sum_mul, ← add_mul]; refine mul_le_mul_of_nonneg_right (le_trans (add_le_add_left hx' _) (le_of_eq ?_)) (by linarith:0 ≤ r'); unfold U; ring
   · rw [← sum_mul,← add_mul]; exact mul_le_mul_of_nonneg_right (le_trans (add_le_add_left hx' _) (le_of_eq (add_comm ..))) hu
   rw [h₂,hV,tuneD,add_comm];rfl
end YM.Trace.Shunt
