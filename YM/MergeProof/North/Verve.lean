import YM.MergeProof.Buys
import YM.MergeProof.North.Clause
import YM.MergeProof.Weathervane

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Float
open Function Filter Lattice Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon MeasureTheory Motion
open scoped Topology BigOperators Classical
variable {ι:Type*}{G:Gauge}{n c:Side}{R:Rep G n} {m N p:ℕ}(t:Motion)
lemma conduits (x:Site n)(q:ℕ→ Config G n→ℂ)(h:Dominated q) (A:R.activities.Moves t.1 x): Dominated (fun i=> stepUp t x (q (A.kp.symm i))):=by obtain ⟨w,hP,hW⟩:=h; exact ⟨_,(Summable.comp_injective hP A.kp.symm.injective),fun i U=> (norm_scalar ..).trans_le (hW (A.kp.symm i) _)⟩
lemma summer [DecidableEq ι] (F:ι→ℂ)(v:Finset ι):scalar t (∑ i∈v,F i)=∑ i∈v,scalar t (F i):=by cases t with | mk s u=> cases u; exact rfl; exact star_sum ..
section
variable (H:History G)(h:H.Selected)(hm: m ≤ N)(x:Site (H.S.side m p)) (P:Config G (H.S.side m p)→ℂ){q:ℕ→ Config G (H.S.side m p)→ℂ} (A:(H.rep N p m).activities.Moves t.1 x)
local notation "vS"=> H.S.side m p
local notation "Q"=> H.rep N p m
open WardBin.Wheels
include h hm A
lemma warble : coin (Q) (stepUp t x P) (fun i=> stepUp t x (q (A.kp.symm i)))=stepUp t x (coin (Q) P q):=by
   funext i; unfold coin stepUp; simp_rw [rep_spins t.1 h hm _ x, prices_steady t.1 h hm i x,scalar_add,scalar_mul, Motion.scalar_real]; congr 1; apply congr_arg
   rw [scalar_tsum]; nth_rw 1 [← A.kp.finsetCongr.tsum_eq]; refine tsum_congr fun j=>?_ ; unfold Accent.nickel; rw [Equiv.finsetCongr_apply,admitted A]; split_ifs
   · rw [summer, Finset.sum_map]; apply sum_congr rfl; intro z hz; rw [scalar_mul]; congr 1; · simp
     rw [← Finset.map_erase,Finset.prod_map]
     have he := fun z=> A.valuesK z i; simp_rw [Equiv.coe_toEmbedding,he, ← Complex.ofReal_prod]; exact (Motion.scalar_real ..).symm
   exact (scalar_z ..).symm
-- profile-aligned Coin also transported (use plus)
include x t
lemma opals {w:ℕ→ Config G (H.S.side m p)→ℂ}(hq:Dominated q)(hr:Dominated w)(hp:profile (Q).activities w = floatUp t x (profile (Q).activities q)): coin (Q) (stepUp t x P) w=stepUp t x (coin Q P q):=by
   let f(i):= stepUp t x (q (A.kp.symm i)); have hi:profile (Q).activities f= floatUp t x (profile (Q).activities q):= roam t x A (by intro i U; unfold f;simp); exact (coin_port Q _ hr (conduits t x q hq A) (hp.trans hi.symm) (h.represents _ _ _ hm|>.good.labels)).trans (warble t H h hm x P A)
end
end YM.MergeProof.Float
