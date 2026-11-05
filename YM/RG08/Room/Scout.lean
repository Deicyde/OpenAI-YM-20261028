import YM.RG08.Room.Kettle

/-!
# Carry a centered, partially external propagator through a change on fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Forms Glyph Cloud Finset Function MvPolynomial
open scoped PowerSeries BigOperators Topology Classical
variable {I J : Type}[Fintype I][Fintype J]
namespace Haze
variable {H : Haze I}{H' : Haze J}

 set_option linter.unusedSectionVars false
/- To do induction we can prove at Heat/series via all powers commuting. Define normalized
 transfer of full (mean-retaining) wick by cancellation of non-symmetric pairs. -/
structure Scout (H : Haze I)(H' : Haze J)(x:I→Port J)(L:I→J→ℝ) : Prop where
 warm (i):i∈H.foam→ x i=∑ j∈H'.foam,L i j • rod j
 cold (i):i∉H.foam → Abroad H'.foam (x i)
 shake (i k):i∈H.foam→k∈H.foam→
      (∑ a∈H'.foam,∑ b∈H'.foam, H'.price a b* L i a * L k b)= H.price i k

variable {x:I→Port J}{L:I→J→ℝ}
private lemma pin_piece (h:Scout H H' x L){j:J}(hj:j∈H'.foam)(i:I):pin j (x i)=if i∈H.foam then L i j • 1 else 0:=by
 split_ifs with hi
 · rw [h.warm i hi,map_sum];simp_rw [Derivation.map_smul,pins,smul_ite,smul_zero,sum_ite_eq,hj,if_true]
 exact h.cold i hi j hj

private lemma plate_pair (h:Scout H H' x L)(a b:J)(p:Port I)(ha:a∈H'.foam)(hb:b∈H'.foam):
 pin a (pin b (belt x p))=∑ i∈H.foam,∑ j∈H.foam,(L i b * L j a) • belt x (pin j (pin i p)):=by
 have he{b:J}(hb:b∈H'.foam)(p:Port I):pin b (belt x p)=∑ i∈H.foam,L i b • belt x (pin i p):=by
   rw [belt_chain,←Finset.sum_subset (s₁:=H.foam) (subset_univ _) (fun i _ hi=>?_)]
   · apply sum_congr rfl;intro i hi;rw [pin_piece h hb,if_pos hi,mul_smul_comm,mul_one]
   rw [pin_piece h hb,if_neg hi,mul_zero]
 rw [he hb,map_sum];simp_rw [Derivation.map_smul,he ha,Finset.smul_sum,smul_smul]

def sauna (H:Haze I):Port I→ₗ[ℝ] Port I:=slab (half H.price) (fun i=>pin i)
lemma sauna_do (p:Port I):sauna H p=∑ a∈H.foam,∑ b∈H.foam, half H.price a b • pin a (pin b p):=by
 rw [sauna,slab_do];symm
 calc
 _ =∑ a∈H.foam,∑ b:I, half H.price a b • pin a (pin b p):=Finset.sum_congr rfl fun i _=>sum_subset (subset_univ _) fun j _ hj=>by rw [half,H.dryR i j hj];simp
 _ = _:=sum_subset (subset_univ _) fun i _ hi=>sum_eq_zero fun j _=>by rw [half,H.dryL i j hi];simp
lemma temperature (h:Scout H H' x L)(p:Port I): sauna H' (belt x p)=belt x (sauna H p):=by
 rw [sauna_do,sauna_do];simp_rw [map_sum,_root_.map_smul]
 have ht(a b:J)(ha:a∈H'.foam)(hb:b∈H'.foam):half H'.price a b • pin a (pin b (belt x p))=
    ∑ i∈H.foam,∑ j∈H.foam,(half H'.price a b*L j a*L i b) • belt x (pin j (pin i p)):=by
    rw [plate_pair h _ _ _ ha hb];simp_rw [Finset.smul_sum,smul_smul];apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;congr 1;ring
 rw [Finset.sum_congr rfl (fun a ha=>Finset.sum_congr rfl (fun b hb=>ht a b ha hb)),Glyph.square H'.foam H'.foam H.foam H.foam (fun a b i j=> (half H'.price a b*L j a*L i b) • belt x (pin j (pin i p)))]
 rw [Finset.sum_comm (s:=H.foam) (t:=H.foam)];apply Finset.sum_congr rfl;intro i hi;apply Finset.sum_congr rfl;intro j hj
 simp_rw [←Finset.sum_smul];congr 1
 simp only [half,←h.shake i j hi hj, Finset.sum_div];apply Finset.sum_congr rfl;intro a _;apply Finset.sum_congr rfl;intro b _;ring

/-- Pure specialization in fields (including killing white for the centered Wick), angle uniforms. -/
def stripped (H:Haze I) (i:I):Port I:=liftInn (H.stop i)

lemma stripped_view (p:Port I)(e:ℕ):tap e (belt H.stripped p)=MvPolynomial.aeval H.stop (tap e p):=by
 have ht(f:Inn I):lug H.stripped f=liftInn (MvPolynomial.aeval H.stop f):=by
   induction f using MvPolynomial.induction_on with
   | C r=> unfold lug;rw [aeval_C,aeval_C,PowerSeries.algebraMap_apply]
   | add p q hi hj=>rw [map_add,map_add,hi,hj,map_add]
   | mul_X p i h=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,h,aeval_X];rw [lug,aeval_X];rfl
 change tap e (spool (lug _) p)=_;rw [ships];simp_rw [ht]
 have he : MvPolynomial.aeval H.stop (tap e p)=tap e (spool (PowerSeries.C : Inn I→Cab (Inn I)) (PowerSeries.map (MvPolynomial.aeval H.stop).toRingHom p)):=by rw [direct,tap]; unfold tap;rw [PowerSeries.coeff_map];rfl
 rw [he,ships];simp [tap]

omit [Fintype I] in
lemma spent (h:Scout H H' x L)(i:I):belt H'.stripped (x i)=belt x (H.stripped i):=by
 by_cases hi:i∈H.foam
 · rw [show H.stripped i=0 from by simp [stripped,stop,hi],map_zero,h.warm i hi,map_sum]
   apply Finset.sum_eq_zero;intro j hj;rw [_root_.map_smul,belt_x,show H'.stripped j=0 from by simp [stripped,stop,hj],smul_zero]
 rw [show H.stripped i=rod i from by simp [stripped,stop,hi,rod],belt_x,abroad_belt (h.cold i hi) (y:=rod) (fun i hi=>by simp [rod,stripped,stop,hi]),belt_id]

lemma seating (h:Scout H H' x L)(p:Port I): belt H'.stripped (belt x p)=belt x (belt H.stripped p):=by
 change ((belt H'.stripped).comp (belt x)) p=((belt x).comp (belt H.stripped)) p
 rw [switched,switched,funext (spent h)]

lemma sauna_read (p:Port I)(e:ℕ): tap e (sauna H p)=radiator H.price (tap e p):=by
 simp only [sauna,slab_do,tap,radiator,axes,map_sum,PowerSeries.coeff_smul,pin,flight_apply]

def heated (H:Haze I)(n:ℕ)(p:Port I):Port I:=rfactor n • (H.sauna)^[n] p
lemma heater_read (i)(p:Port I)(e): tap e (H.heated i p)=gust H.price i (tap e p):=by
 have hz:tap e (H.sauna^[i] p)= (radiator H.price)^[i] (tap e p):=by
    induction i with
    | zero=>rfl
    | succ i h=>rw [iterate_succ_apply',iterate_succ_apply',sauna_read,h]
 unfold heated gust;rw [show tap e (rfactor i • H.sauna^[i] p)=rfactor i • tap e (H.sauna^[i] p) from PowerSeries.coeff_smul ..,hz]

lemma explores (h:Scout H H' x L)(n:ℕ)(p:Port I):H'.heated n (belt x p)= belt x (H.heated n p):=by
 have he (n:ℕ):H'.sauna^[n] (belt x p)=belt x (H.sauna^[n] p):=by induction n with
 | zero=>rfl
 | succ n ih=>rw [iterate_succ_apply',ih,temperature h,iterate_succ_apply']
 unfold heated;rw [he,_root_.map_smul]

private lemma admission (H:Haze I)(f:Port I)(e:ℕ):∃ n,∀ k≤e,Halt H.price (tap k f) n:=by
 induction e with
 | zero=>obtain ⟨n,hn⟩:=halts H.price H.flipped (tap 0 f);exact ⟨n,fun k hk=>by simpa [show k=0 by omega] using hn⟩
 | succ e h=>
   obtain ⟨n,hn⟩:=halts H.price H.flipped (tap (e+1) f)
   obtain ⟨m,hm⟩:=h
   refine ⟨m+n,fun k hk i hi=>?_⟩
   rcases Nat.lt_or_eq_of_le hk with hk|rfl
   · exact hm k (by omega) i (by omega)
   exact hn _ (by omega)

def blower (H:Haze I)(n:ℕ)(f:Port I):Port I:=belt H.stripped (∑ i∈range n,H.heated i f)
lemma held (H:Haze I){n:ℕ}{f:Port I}{e:ℕ}(h:Halt H.price (tap e f) n):tap e (H.brew f)=tap e (H.blower n f):=by
 rw [blower,brew_view,stripped_view,stove_does]; change aeval H.stop (wick _ _)=_; congr 1; rw [wick_budget h]; unfold tap at *;rw [map_sum]; exact sum_congr rfl (fun i _=> (heater_read i f e (H:=H)).symm)

theorem entrusted (h:Scout H H' x L)(p:Port I):H'.brew (belt x p)=belt x (H.brew p):=by
 ext e :1
 obtain ⟨n,hn⟩:=admission H p e;obtain ⟨m,hm⟩:=admission H' (belt x p) e
 change tap e _=tap e _
 rw [held H' (n:=m+n) (fun i hi=>hm e le_rfl i (by omega)),steady_belt x e _ (H.blower (m+n) p) (fun i hi=>held H (n:=m+n) (fun l hl=>hn i hi l (by omega)))]
 unfold blower; simp_rw [explores h,←_root_.map_sum,seating h]

end Haze
end YM.RG08.Room
