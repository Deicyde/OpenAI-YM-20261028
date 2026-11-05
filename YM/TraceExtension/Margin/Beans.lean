import YM.TraceExtension.Margin.Sky
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
open Zn
variable {F:Frame G 4}{Z:Frame G 5}{n:Side}{t:ℝ}{R:Rep G n}{J:Dart G n}
open Stationary Exterior Tree Filch Lamp Loft Xo Pills
open Det Fen Shepherd AnalyticBridge VerifiedReset Swift
variable {a b c:ℝ}{T:SectionData Z}{S:Stage}{k m q:ℕ}{U:Finset GreenA}{Q L:Finset ℕ}
-- contact-safe supplier. Literal θ not rem. price tests via Holt invariant
set_option maxHeartbeats 480000 in
lemma brass (a:G.ColorIndex)(hG:G.Simple)(hp:Wealth S R t J)(hm:Merch R t J U Q k)(ha: Craft S t R J m b) (he:Nonwrapping (tempQ t (n:=n)) 0)(hn:20*(high t+rim t+10)< n.val)(hv:5≤ R.p.order)(hh:R.p.threshold=thetaP t) (X:Axis→ Coefficient Z n) (hT:∀ i,Combat T H R t J U Q L k q i (X i)) :
    ‖Revise R (fun i=> (X i).x)‖ ≤ Wave (1/6) t ∧
    |MintR Z hG (Revise R (fun i=> (X i).x))-midPay a J/12| ≤4*‖MintR Z hG‖*Wave (-1) t + calorie t/12:=by
    let V:=fun i=>(X i).x;let z:=YCore t J; let P:= MintR Z hG; let u:= (R.p.threshold^(2:ℕ))⁻¹; have hp' :0<u:=by unfold u; positivity[R.p.threshold_pos]
    have hz(W:Axis → Z.Coeff)(x:ℝ)(hx:0 ≤ x)(h:∀ i,Z.coeffSize (W i) ≤ (thetaP t)^ (2:ℕ) *x) : ‖u • W‖ ≤ x:=by
        rw[pi_norm_le_iff_of_nonneg hx]; intro i; change ‖u • W i‖≤x; rw[norm_smul,Real.norm_of_nonneg hp'.le]; exact (mul_le_mul_of_nonneg_left ((Push.Local.norm_le_size ..).trans (h i)) hp'.le).trans_eq (by rw[← hh,← mul_assoc,show u*R.p.threshold^ (2:ℕ)=1 from by unfold u; field_simp [(R.p.threshold_pos).ne'],one_mul])
    have hX(i): Z.coeffSize (V i) ≤ grantS t:=by obtain ⟨x,hx,h⟩:=(hT i).charge.charge; exact (le_add_of_nonneg_right (rem_nonneg h)).trans hx
    refine ⟨hz V _ (Zn.wake ..).le hX,?_⟩
    let F(w:Peat G n):= altoD R t H Z w; let K(i):= rill (quietL R t Q) (z i); let D(i):=swellW R Q t z i; let y(i):=rimW R Q t z i; let B(i):=stubJ (lush (z i)); let W:= fun i=> F (relic R J t U i); let E:=fun i=> F (Weir.kerr t k (z i) (ochre R t U Q)); let L':= fun i=> addUp R t J k q U Q L H Z i
    have hb(i): y i + D i=K i:= eq_sub_iff_add_eq.mp (hm.weld i); have hy(i): K i∈ loom G n:= hb i ▸ (loom _ _).add_mem (hm.loop _).silk (hm.lones _).silk
    have ht(i): filmR (K i)=filmR (y i)+filmR (D i):=by rw[← hb]; exact (plush (tempQ t) _ _ R t).1
    have hy'(i):= Real_regular (hm.loop i).puff.regular; have hc'(i):= Real_regular (hm.lones i).puff.regular
    have hr(i): R.p.Regular (tempQ t) (filmR (K i)):= ht i ▸ regular_add (hy' i) (hc' i)
    have hV: V=W+ F ∘ B - (F ∘ K) + F ∘ D+ E + L':=by
        have hx (i): F (rimW R Q t z i)= F (K i)-F (D i):=by apply eq_sub_of_add_eq; unfold F altoD Push.Local.weighted; rw[ht,Push.Local.project_add H _ (hy' i) (hc' i) hv,map_add,map_add]
        ext1 i; rw[show V i=tuneD U Q L t R J k q H Z i from (hT i).stick]; simp only [Pi.add_apply,Pi.sub_apply,Function.comp_apply]; change W i+F (B i)-F (rimW R Q t z i) + E i+ L' i=_; rw [hx]; abel
    have hp : P (u • (F ∘ K))=0:=by
       change MintR Z hG (Revise R fun i=>altoD R t H Z (K i))=_;rw [mack a K hy hr hG hv he (by omega),show Holt a _=0 from hm.bloom a hn];simp
    have he1: P (u • (F ∘ B))=(Holt a (fun i=> B i ∘input G n)).re/12:=mack a _ (fun i=>(‹Wealth S R t J›.mids i).silk) (fun i=> Real_regular (‹Wealth S R t J›.mids i).puff.regular) hG hv he (by omega)
    let v:= Wave (-1) t; let z':= ‖P‖*v; have hP (w:Axis→Z.Coeff)(h:∀ i,Z.coeffSize (w i)≤ stepX t): |P (u • w)|≤ z':=(P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hz _ v (Zn.wake ..).le h) (norm_nonneg _))
    have hw:= abs_le.mp (hP W (fun i=>(hT i).phase)); have h₄ := abs_le.mp (hP (F ∘ D) (fun i=>(hT i).march)); have h₅:= abs_le.mp (hP E (fun i=>(hT i).lower)); have h₆:= abs_le.mp (hP L' (fun i=> (hT i).money.trans (mul_le_mul_of_nonneg_left (Zn.wane t (by norm_num:(-(2:ℝ)) ≤ -1)) (sq_nonneg _))))
    change |P (u • V)-_| ≤ _; rw[hV,smul_add,smul_add,smul_add,smul_sub,smul_add,map_add,map_add,map_add,map_sub,map_add,hp,he1]
    rw[abs_le]; have hp:= abs_le.mp (ha.earning a); let y':=(Holt a (fun i=> B i∘input G n)).re
    change _ ∧ _; change -_ ≤ midPay a J-y' ∧ midPay a J-y' ≤ _ at hp
    change -(_+_)≤ _+y'/12-0+_+_+_-_ ∧ (_+y'/12-0+_+_+_-_ )≤4*‖P‖*v+_;
    unfold z' at *; constructor <;> linarith only [hw,h₄,h₅,h₆,hp]
end YM.Trace.Margin
