import YM.TraceExtension.Quince.Ride
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Source.Drops
open Push.Local (Probe)
open Push Planned.PrimaryIntegral295 PPX Flutes Place Bazaars Exterior Streets Postcards WardBin.Lies Cabins Bid
open Next Next.Foundations JointLoad JointLoad.Heir Bloch Carrier Next.Free Laurent Cub Finset
open MultiNext.SignedSource
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {n c f:Side}
variable {k p d r j u:ℕ}{B:BudgetPoint}{S:StepData c f}{T:Tube G S}
lemma sep_cost (q:Ratio c f)(x y:Site c): separation (q.embed x) (q.embed y) ≤ q.count.val * separation x y:=by
   unfold separation; rw[← q.root_embed, ← q.root_embed,← map_sub,q.root_embed]
   apply Finset.sup_le; intro i _; rw [q.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ (component_le _ _)
def depthW (b: Side)(m:ℕ):= b.val*(m+2)
lemma sep_fore (q: Ratio c f)(x y:Site f) (h:separation (q.parent x) (q.parent y) ≤ r): separation x y ≤ depthW q.count r:=by
    unfold depthW; have hy:= Corona.near q y; have hx:=Corona.near q x; have hm:= (sep_cost q (q.parent x) (q.parent y)).trans (Nat.mul_le_mul_left _ h); have h:= separation_triangle x (q.embed (q.parent x)) y; have ht:= separation_triangle (q.embed (q.parent x)) (q.embed (q.parent y)) y; rw [separation_comm (q.embed (q.parent y)) y] at ht
    rw [mul_add]
    omega
section Buffer
variable {B P:BudgetPoint}{b m R:ℕ}{Y:Support c}{X:Support f}(hi:20*(m+b+1)< c.val)(hh:∀ i∈X,halo b {(S.ratio.parent i)}⊆Y)(hY:∀ i∈Y,separation 0 i ≤ m)
lemma anchor0 (q:Ratio c f): q.parent 0=0:=by rw[← q.root.map_zero]; exact q.embed_parent _
include hh hY
lemma facesBound (i:Site f)(he:i∈X):separation i 0 ≤ depthW S.ratio.count m:=by apply sep_fore S.ratio; rw [anchor0, separation_comm]; exact hY _ (hh i he (halo_subset _ _ (Finset.mem_singleton_self _)))
include hi
lemma roomK (i:Site f)(he:i∈X) : let p:=S.ratio.parent i
    cellar (S.ratio.count) (lift i)= lift p:=by
    intro p; let q:= S.ratio; let w:= cellar q.count (lift i)
    have hv: p=wrap c w:=by unfold p; nth_rw 1 [← wrap_lift i]; exact Streets.owner ..
    have hx :=facesBound hh hY i he
    apply Eq.symm; apply lift_eq_iff.mpr; refine ⟨hv,fun j=>?_⟩
    let L:=q.count.val; have hL:L>0:=q.count.property; have ht: (lift i j).natAbs ≤ L*(m+2):= (component_le ..).trans (by simpa only[separation, depthW,sub_zero] using hx)
    have hy := balance q.count (lift i); let v:=wrap q.count (lift i)
    have he := lift_centers v j
    have hh: lift i j=lift v j+(L:ℤ)*w j:= by exact (congr_fun hy j).trans (by simp[L,w,v,nsmul_eq_mul])
    have hc: -(L:ℤ) <2*lift v j ∧ 2*lift v j ≤ L:=he
    have hl : -((L:ℤ)*((m:ℤ)+2)) ≤ lift i j∧lift i j ≤ (L:ℤ)*((m:ℤ)+2):= by exact_mod_cast (by omega : -(((L*(m+2):ℕ):ℤ)) ≤ lift i j∧ lift i j ≤ ((L*(m+2):ℕ):ℤ))
    have hA:0 < (L:ℤ):=by positivity
    have H': 2*((m:ℤ)+3)<c.val:=by omega
    change -(c.val:ℤ)<2*w j∧2*w j ≤ _; constructor
    · apply lt_of_mul_lt_mul_left (_ : (L:ℤ)*_ < L*(2*w j)) hA.le; linarith only [mul_lt_mul_of_pos_left H' hA,hl.1,hc.2,hA,hh]
    apply le_of_mul_le_mul_left (_ : (L:ℤ)*(2*w j) ≤ L*_) hA; linarith only [mul_lt_mul_of_pos_left H' hA,hl.2,hc.1,hA,hh]
lemma marginW (i:Site f)(he:i∈ X)(z:Cover)(hz:size z ≤ b): let w:=cellar S.ratio.count (lift i)+z
    separation 0 (wrap c w) ≤ m ∧ lift (wrap c w)=w:=by
    intro w; let q:= S.ratio; let p:=q.parent i
    have hq := roomK hi hh hY i he
    have hx:wrap c w=p+wrap c z:=by unfold w; rw[hq, map_add,wrap_lift]
    have ht:∀ r∈ halo b {p}, separation 0 r ≤ m:= fun r hr=> hY r (hh i he hr)
    have hh:separation 0 p ≤ m:=ht _ (halo_subset _ _ (Finset.mem_singleton_self _)); have hp:separation 0 (wrap c z) ≤ b:= (Cabins.spans ..).trans hz
    refine ⟨hx.symm ▸ ht _ (halo_spec.mpr ⟨p,Finset.mem_singleton_self _,?_⟩),lift_eq_iff.mpr ⟨rfl,fun j=>?_⟩⟩
    · rw [← separation_translate 0 (wrap c z) p] at hp; simpa [add_comm] using hp
    have hz (i:Axis): (z i).natAbs≤ b:= (Finset.single_le_sum (s:=Finset.univ) (f:=fun i=> (z i).natAbs) (fun _ _=>Nat.zero_le _) (Finset.mem_univ _)).trans hz
    have he := (component_le p j).trans (show pdist p ≤ m from by simpa [separation] using hh); change -_ <2*((cellar q.count _+z) j) ∧ 2*(cellar q.count _+z) j≤_; rw [hq]; have hp:=hz j; simp only [Pi.add_apply]; unfold p q at he; omega
end Buffer
end YM.PhysicalNext.Repeat.Quince
