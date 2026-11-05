import YM.RG05Readout.Grants.Grain
import YM.RG05Readout.Address.Shaft
/-!
# Pre-side incomes (B, B', exponent recorded after R? no)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Copper
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native Address
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets OPE
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{m N p n d:ℕ}
-- reserve 1/3 shrink (room beyond). τ=1/3
abbrev trim (P:Side):ℝ:= (P.val:ℝ)^(-(1:ℝ)/3)
abbrev lamp (P:Side)(j:ℕ):= (P.val:ℝ)^((1:ℝ)/((j:ℝ)+1))
variable (d j N:ℕ)(L:Side) (P:Stage) (c K B B' Q β:ℝ)
abbrev roughT (P:Stage):= turnCost P.order P.power

def debt (d:ℕ)(L:Side)(K c:ℝ)(P:Stage):= decay d L K c (Doors.rate L)*roughT P
def grant (d:ℕ)(L:Side)(K c:ℝ)(P:Stage):= margin d c K*((L.val:ℝ)⁻¹)+debt d L K c P
structure Crossed :Prop where
   warm : ((L.val:ℝ)⁻¹)*B ≤ 1
   lapse: debt d L K c P * B ≤ 1
   small: ((L.val:ℝ)⁻¹)*(2*margin d c K+1)+debt d L K c P * B + margin d c K*(((L.val:ℝ)⁻¹)*B) ≤ trim L
   fares : Q*(trim L+oldCost d K* Doors.rate L)≤ 1/2
   sink : (1+B'*2)*grant d L K c P ≤ trim L
   modest : 2*Q+ beamCost d c K + (1+oldCost d K) ≤ lamp L j
   supp : B+B' ≤ lamp L j
   tickets : 2*tollP d K c β+tollV d L K c (Doors.rate L) β*roughT P*B ≤ lamp L j
   -- also stencil grade strong graph needed later
-- numeric eventually.Real dependence formulate via n Side; Side Order/tendsto
def levelR (i:ℕ):Side:=⟨i+1,Nat.succ_pos _⟩
lemma eventual : ∃ k:ℕ,∀ L:Side,k≤L.val → Crossed d j L P c K B B' Q β:=by -- independent K-system costs numeric
    let x (n:ℕ):ℝ:= (levelR n).val
    have hx:Tendsto x atTop atTop:= tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (f:=id) (g:=fun i:ℕ=>i+1) (fun i=>i.le_succ) tendsto_id)
    have ht(e:ℝ)(he:0<e): Tendsto (fun i=>x i^(-e)) atTop (𝓝 0):= (tendsto_rpow_neg_atTop he).comp hx
    let a:= (1:ℝ)/3; let b:=(2:ℝ)/5
    let F':= fun n=> (x n)^(-a)
    have he:Tendsto F' atTop (𝓝 0):=ht a (by norm_num [a]); let u (i):=(x i)⁻¹
    have hu:Tendsto u atTop (𝓝 0):= tendsto_inv_atTop_zero.comp hx
    have hQ:Tendsto (fun i => (x i)^a*u i) atTop (𝓝 0):=by
        refine (ht (1-a) (by norm_num [a])).congr (fun i=> ?_)
        have ht0 : 0< x i:=by unfold x;positivity
        rw [show -(1-a) = a+(-(1:ℝ)) by ring, Real.rpow_add ht0]; rw [Real.rpow_neg_one]
    let v i:= debt d (levelR i) K c P
    let μ i:= (x i)^(-b)
    have hv:Tendsto v atTop (𝓝 0):=by
        simpa only [v,debt,Address.decay,Doors.rate, μ,b, u, x, mul_zero,zero_mul,add_zero] using (((ht b (by norm_num [b])).const_mul (stCost d K+aCost d K)).add (show Tendsto (fun i=> u i * (2*(c+μ i))) atTop (𝓝 (0*(2*(c+0)))) from hu.mul (((tendsto_const_nhds (x:=c)).add (ht b (by norm_num [b]))).const_mul 2))).mul_const (roughT P)
    have hμ:Tendsto μ atTop (𝓝 0):=ht b (by norm_num [b])
    have hj:Tendsto (fun i=> (x i)^a*μ i) atTop (𝓝 0):=(ht (b-a) (by norm_num [a,b])).congr fun i=> by unfold μ; rw [← Real.rpow_add (by dsimp [x]; positivity),show -(b-a)=a+-b by ring]
    have hδ:Tendsto (fun i=>(x i)^a*v i) atTop (𝓝 0):=by
        refine Tendsto.congr ?_ (by simpa only [zero_mul,zero_add] using ((hj.mul_const (stCost d K+aCost d K)).add (hQ.mul (hμ.const_add c|>.const_mul 2))).mul_const (roughT P))
        intro i; unfold v debt decay; change ((x i)^a*μ i*(stCost d K+aCost d K)+(x i)^a*u i*(2*(c+μ i)))*_= x i^a* ((_*μ i+ u i* (2*(c+μ i))) *_); ring
    let f i:= grant d (levelR i) K c P
    have hF:Tendsto (fun i=>(x i)^a*f i) atTop (𝓝 0):= Tendsto.congr (fun i=> by unfold f grant; change x i^a *u i*margin d c K +_ = x i^a*(margin d c K*u i+v i); ring) (show Tendsto (fun i=> (x i^a*u i)* margin d c K+ x i^a*v i) atTop (𝓝 0) from by simpa only [zero_mul,zero_add] using (hQ.mul_const (margin d c K)).add hδ)
    have hw:Tendsto (fun i=> lamp (levelR i) j) atTop atTop:=(tendsto_rpow_atTop (show 0< (1:ℝ)/((j:ℝ)+1) by positivity)).comp hx
    have hE : ∀ᶠ i in atTop,Crossed d j (levelR i) P c K B B' Q β:=by
        let z i:= tollV d (levelR i) K c (Doors.rate (levelR i)) β
        have hy:Tendsto z atTop (𝓝 (aCost d K*2)):=by
            have h₁:= hμ.const_add 2
            have h₂:= h₁.add (hμ.const_mul K)|>.const_mul (aCost d K)
            simpa only [z,tollV,Doors.rate, μ, b, u, x,add_zero,mul_zero,zero_mul] using h₂.add (hu.mul ((hμ.const_add 2).const_add (1+c+β)))
        let l i:=2*tollP d K c β+z i*roughT P*B; let l' :=2*tollP d K c β+ aCost d K*2*roughT P*B
        have hl:Tendsto l atTop (𝓝 l'):=((hy.mul_const (roughT P)).mul_const B).const_add (2*tollP d K c β)
        have hX: Tendsto (fun i=>x i^a*u i*(2*margin d c K+1)+x i^a*v i*B+margin d c K*(x i^a*u i*B)) atTop (𝓝 0):=by
            exact add_zero (0:ℝ) ▸ (show Tendsto _ _ _ from (by simpa only [zero_mul,mul_zero,add_zero] using ((hQ.mul_const (2*margin d c K+1)).add (hδ.mul_const B)).add ((hQ.mul_const B).const_mul (margin d c K)))) -- edit
        filter_upwards [(hu.mul_const B).eventually (ge_mem_nhds (by rw [zero_mul]; exact (by norm_num : (0:ℝ) <1))), (hv.mul_const B).eventually (ge_mem_nhds (show _ < (1:ℝ) by ring_nf; norm_num)),hX.eventually (ge_mem_nhds zero_lt_one),((he.add (hμ.const_mul (oldCost d K))).const_mul Q).eventually (ge_mem_nhds (show Q*(0+oldCost d K*0)<1/2 by norm_num)), (hF.mul_const (1+B'*2)).eventually (ge_mem_nhds (by norm_num : 0*(1+B'*2) <(1:ℝ))), hw.eventually_ge_atTop (2*Q+ beamCost d c K +(1+oldCost d K)), hw.eventually_ge_atTop (B+B'), hl.eventually (ge_mem_nhds (lt_add_one l')), hw.eventually_ge_atTop (l'+1)] with i hu hV hX hY ht hL hm h₄ h₅
        have hξ:0<x i:=by dsimp [x];positivity
        have hg : trim (levelR i)=(x i^a)⁻¹:=by unfold trim; rw [neg_div]; exact Real.rpow_neg hξ.le a
        refine ⟨hu,hV,?_,?_,?_,hL,hm,le_trans h₄ h₅⟩
        · rw [hg, ←one_div (x i^a), le_div_iff₀ (Real.rpow_pos_of_pos hξ _)]
          change (u i*_+v i*B+_ * (u i*_)) * _ ≤ _; linarith only [hX]
        · rw [show trim (levelR i)= F' i from by unfold trim; rw [neg_div]]; exact hY
        rw [hg,←one_div (x i^a),le_div_iff₀ (Real.rpow_pos_of_pos hξ _)]
        change (1+B'*2) * f i * _ ≤ _; linarith only [ht]
    obtain ⟨k,hk⟩:= eventually_atTop.mp hE
    refine ⟨k+1,fun L hl=>?_⟩; obtain ⟨i,hi⟩:= Nat.exists_eq_add_of_le (show 1 ≤ L.val from L.property) -- edit
    have he : L=levelR i:=Subtype.ext (by change L.val=i+1; omega)
    apply he.symm ▸ hk i (by omega)
end YM.RG05Readout.Copper
