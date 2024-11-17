/*
    Copyright (C) 2023 MrSpike63

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as published by
    the Free Software Foundation, version 3.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

#pragma once
#include "curve_math.h"
#include "keccak.h"
#include "math.h"


__global__ void __launch_bounds__(BLOCK_SIZE, 2) gpu_contract2_address_work(
    int score_method, Address a, _uint256 prefix_uint256, int prefix_bits, _uint256 base_random_key, _uint256 bytecode) {
    uint64_t thread_id = (uint64_t)threadIdx.x + (uint64_t)blockIdx.x * (uint64_t)BLOCK_SIZE;
    uint64_t key_offset = (uint64_t)THREAD_WORK * thread_id;

    _uint256 key = base_random_key;
    asm(
        "add.cc.u32 %0, %0, %8;     \n\t"
        "addc.cc.u32 %1, %1, %9;    \n\t"
        "addc.cc.u32 %2, %2, 0x0;   \n\t"
        "addc.cc.u32 %3, %3, 0x0;   \n\t"
        "addc.cc.u32 %4, %4, 0x0;   \n\t"
        "addc.cc.u32 %5, %5, 0x0;   \n\t"
        "addc.cc.u32 %6, %6, 0x0;   \n\t"
        "addc.u32 %7, %7, 0x0;      \n\t"
        : "+r"(key.h), "+r"(key.g), "+r"(key.f), "+r"(key.e), "+r"(key.d), "+r"(key.c), "+r"(key.b), "+r"(key.a) : "r"((uint32_t)(key_offset & 0xFFFFFFFF)), "r"((uint32_t)(key_offset >> 32))
    );
    
    int random_bits = 256 - prefix_bits;
    _uint256 shifted_random_bits = cpu_shift_left_256(key, prefix_bits);
    
    _uint256 salt = cpu_or_256(prefix_uint256, shifted_random_bits);
    
    for (int i = 0; i < THREAD_WORK; i++) {
        handle_output2(score_method, calculate_contract_address2(a, salt, bytecode), key_offset + i);
    
        // Increment the random bits portion of the salt
        increment_random_bits_in_salt(&salt, prefix_bits);
    
        // Alternatively, increment 'key' and recombine
        key.h += 1; // Increment the least significant part of the random bits
        shifted_random_bits = cpu_shift_left_256(key, prefix_bits);
        salt = cpu_or_256(prefix_uint256, shifted_random_bits);
    }
}
