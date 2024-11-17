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
    int score_method, Address a, _uint256 base_key, _uint256 bytecode, 
    SaltPrefix salt_prefix) {
    
    // Debug output for thread 0 only
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        printf("Debug - Salt prefix length: %d\n", salt_prefix.length_bytes);
        printf("Debug - Salt prefix: %08x%08x%08x%08x%08x%08x%08x%08x\n",
               salt_prefix.prefix.a, salt_prefix.prefix.b, salt_prefix.prefix.c, 
               salt_prefix.prefix.d, salt_prefix.prefix.e, salt_prefix.prefix.f,
               salt_prefix.prefix.g, salt_prefix.prefix.h);
    }

    uint64_t thread_id = (uint64_t)threadIdx.x + (uint64_t)blockIdx.x * (uint64_t)BLOCK_SIZE;
    uint64_t key_offset = (uint64_t)THREAD_WORK * thread_id;

    _uint256 key = base_key;
    asm(
        "add.cc.u32 %0, %0, %8;     \n\t"
        "addc.cc.u32 %1, %1, %9;    \n\t"
        "addc.cc.u32 %2, %2, 0x0;   \n\t"
        "addc.cc.u32 %3, %3, 0x0;   \n\t"
        "addc.cc.u32 %4, %4, 0x0;   \n\t"
        "addc.cc.u32 %5, %5, 0x0;   \n\t"
        "addc.cc.u32 %6, %6, 0x0;   \n\t"
        "addc.u32 %7, %7, 0x0;      \n\t"
        : "+r"(key.h), "+r"(key.g), "+r"(key.f), "+r"(key.e), "+r"(key.d), "+r"(key.c), "+r"(key.b), "+r"(key.a) 
        : "r"((uint32_t)(key_offset & 0xFFFFFFFF)), "r"((uint32_t)(key_offset >> 32))
    );

    // Create a mask for the prefix bytes
    _uint256 mask = {0};
    if (salt_prefix.length_bytes > 0) {
        int remaining_bytes = salt_prefix.length_bytes;
        for (int i = 0; i < 8 && remaining_bytes > 0; i++) {
            uint32_t* word = &mask.a + i;  // Changed from (7-i) to i
            int bytes_in_word = min(4, remaining_bytes);
            *word = 0xFFFFFFFF >> ((4 - bytes_in_word) * 8);
            remaining_bytes -= bytes_in_word;
        }
    }

   /* // Debug output for thread 0 only
    if (threadIdx.x == 0 && blockIdx.x == 0) {
        printf("Debug - Mask: %08x%08x%08x%08x%08x%08x%08x%08x\n",
               mask.a, mask.b, mask.c, mask.d, mask.e, mask.f, mask.g, mask.h);
        
        _uint256 first_salt = key;
        first_salt.a = (first_salt.a & ~mask.a) | (salt_prefix.prefix.a & mask.a);
        first_salt.b = (first_salt.b & ~mask.b) | (salt_prefix.prefix.b & mask.b);
        first_salt.c = (first_salt.c & ~mask.c) | (salt_prefix.prefix.c & mask.c);
        first_salt.d = (first_salt.d & ~mask.d) | (salt_prefix.prefix.d & mask.d);
        first_salt.e = (first_salt.e & ~mask.e) | (salt_prefix.prefix.e & mask.e);
        first_salt.f = (first_salt.f & ~mask.f) | (salt_prefix.prefix.f & mask.f);
        first_salt.g = (first_salt.g & ~mask.g) | (salt_prefix.prefix.g & mask.g);
        first_salt.h = (first_salt.h & ~mask.h) | (salt_prefix.prefix.h & mask.h);
        
        printf("Debug - First salt: %08x%08x%08x%08x%08x%08x%08x%08x\n",
               first_salt.a, first_salt.b, first_salt.c, first_salt.d,
               first_salt.e, first_salt.f, first_salt.g, first_salt.h);
    }*/

    for (int i = 0; i < THREAD_WORK; i++) {
        // Combine prefix with random bytes
        _uint256 salt = key;
        salt.a = (salt.a & ~mask.a) | (salt_prefix.prefix.a & mask.a);
        salt.b = (salt.b & ~mask.b) | (salt_prefix.prefix.b & mask.b);
        salt.c = (salt.c & ~mask.c) | (salt_prefix.prefix.c & mask.c);
        salt.d = (salt.d & ~mask.d) | (salt_prefix.prefix.d & mask.d);
        salt.e = (salt.e & ~mask.e) | (salt_prefix.prefix.e & mask.e);
        salt.f = (salt.f & ~mask.f) | (salt_prefix.prefix.f & mask.f);
        salt.g = (salt.g & ~mask.g) | (salt_prefix.prefix.g & mask.g);
        salt.h = (salt.h & ~mask.h) | (salt_prefix.prefix.h & mask.h);

        // Calculate address and score first
        Address contract_addr = calculate_contract_address2(a, salt, bytecode);
        int score = 0;
        if (score_method == 0) { score = score_leading_zeros(contract_addr); }
        else if (score_method == 1) { score = score_zero_bytes(contract_addr); }
        else if (score_method == 2) { score = score_vanity(contract_addr); }

        // Only process if score is high enough
        if (score >= 90) {
            handle_output2(score, contract_addr, salt);
        }
        
        key.h += 1;
    }
}
