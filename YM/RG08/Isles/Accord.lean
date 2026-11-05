import YM.RG08.Isles.Morph
import YM.RG08.Flat.Curl

noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Rows Laurent Finset Function Lattice Filter Bloch
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I J:Type}[Fintype I][Fintype J]{σ B:ℝ}{A:Kernel I J} {T:∀ n:Side,Matrix (Co n I) (Co n J) ℝ}

/- Every-period agreements already from linear supplies, e.g. for Γ, can be used
unchanged in empirical form (not another gauge or copy).
-/
lemma tagged (h:Tagged σ B A T)(hp:0<σ) : StudyCross I J σ ((Fintype.card I+Fintype.card J:ℝ)*B) (fun i=> T (chain i)) A:=by
 have hl:{c:ℕ}→(0:ℝ) ≤ Fintype.card I:=fun {_}=>Nat.cast_nonneg _
 have hj:(0:ℝ) ≤ Fintype.card J:=Nat.cast_nonneg _
 have Cpos:=h.pos
 have hci: (Fintype.card I:ℝ)*B≤(Fintype.card I+Fintype.card J:ℝ)*B:=by nlinarith
 have hcj: (Fintype.card J:ℝ)*B≤(Fintype.card I+Fintype.card J:ℝ)*B:=by have hr:=hl (c:=0); nlinarith
 have hf {I J:Type}[Fintype J]{A:Kernel I J}(h:Priced σ B A)(x:Market I):∑' y,bill (A x y) (σ*sep x.1 y.1) ≤ ENNReal.ofReal ((Fintype.card J:ℝ)*B):=by
    rw [ENNReal.tsum_prod'];simp_rw [tsum_fintype];apply full_sum _ _ h.pos;intro i;simpa [delta] using h.row x i
 have hg {I J:Type}[Fintype J]{A:Kernel I J}{T:∀ n:Side,Matrix (Co n I) (Co n J) ℝ}(h:Tagged σ B A T)(n:Side)(x:Cove n I):∑' y:Cove n J,bill (T n x y) (σ*walk x.1 y.1)≤ ENNReal.ofReal (↑(Fintype.card J)*B):=by
   -- resolve actual displays, bound via hf
   let z:= reach x
   have he:=hf (I:=I) h.toPriced z
   have hh (y: Cove n J):T n x y= display A n z y:=by rw [(h.seen n) z y]; simp [z,reach]
   simp_rw [hh,display]
   apply le_trans _ he
   rw [ENNReal.tsum_prod',ENNReal.tsum_prod' (f:=fun w:Cover×J=>_)] -- terms?
   rw [ENNReal.tsum_comm,ENNReal.tsum_comm (f:=fun (w:Cover) (j:J)=>_)]
   apply ENNReal.tsum_le_tsum; intro j
   calc
    _ ≤ ∑' (y:Site n), ∑' (u:Cover), if wrap n u=y then bill (A z (u,j)) (σ*sep z.1 u) else 0:= ENNReal.tsum_le_tsum fun y=> (bill_tsum ..).trans (ENNReal.tsum_le_tsum fun u=>?_)
    _ ≤ _:=by rw [ENNReal.tsum_comm];simp
   dsimp only
   split_ifs with hi
   · apply bill_mono le_rfl
     apply mul_le_mul_of_nonneg_left _ hp.le
     simpa only [z,reach,wrap_lift,hi] using walk_wrap (P:=n) (lift x.1) u
   simp [bill]
 refine ⟨hp,by positivity,fun x=>(hf h.toPriced x).trans (by gcongr),fun y=> ?_,fun i x=>(hg h _ x).trans (by gcongr),?_,?_⟩
 · simpa only [swap,sep_comm y.1] using (hf (h.toPriced.rear hp.le) y).trans (ENNReal.ofReal_le_ofReal hci)
 · intro i y
   have he (x:colony I i):walk y.1 x.1=walk x.1 y.1:= (shore (chain i) Unit).left (y.1,()) (x.1,())
   simpa only [Matrix.transpose_apply,he,colony] using (hg (h.rear hp.le) _ y).trans (ENNReal.ofReal_le_ofReal hci)
 intro x y
 -- use point resolution by DCT support intersection
 let f (u:Cover):= if u=y.1 then A x (u,y.2) else 0
 have he(i:ℕ): T (chain i) (port (chain i) x) (port (chain i) y)=∑' u:Cover, if wrap (chain i) u=wrap (chain i) y.1 then A x (u,y.2) else 0:=((h.seen _) x (port (chain i) y)).symm
 simp_rw [he]
 have hu(u:Cover) : Tendsto (fun i=> if wrap (chain i) u=wrap (chain i) y.1 then A x (u,y.2) else 0) atTop (𝓝 (f u)):= by
    apply Filter.EventuallyEq.tendsto
    filter_upwards [Next.Free.eventually_unfold chain rise u,Next.Free.eventually_unfold chain rise y.1] with i hi hj
    by_cases hh:u=y.1
    · simp [f,hh]
    simp [f,hh,show wrap (chain i) u≠ wrap (chain i) y.1 from fun he=>hh (hi ▸ hj ▸ congr_arg lift he)]
 have hw:= (summable_from_receipt (fun (z:Cover)=>mul_nonneg hp.le (delta_nonneg 1 x.1 z)) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.row x y.2))).norm
 have ht:= tendsto_tsum_of_dominated_convergence hw hu (.of_forall fun i z=>by split_ifs <;> simp)
 simpa [f,tsum_ite_eq'] using ht
end YM.RG08.Isles
